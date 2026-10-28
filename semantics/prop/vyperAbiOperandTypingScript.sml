(* Raw ABI operand typing. A memory reference describes a decoded cell at an
   address, NOT a path whose index must remain below a later array length.
   TOP-LEVEL: abi_cell_typed, abi_operand_typed; read/stage soundness;
   capture and disjoint-write preservation. No lowering certificate is assumed. *)
Theory vyperAbiOperandTyping
Ancestors
  list rich_list arithmetic pair option words vyperAST vyperValue vyperState
  vyperMisc vyperStorage vyperStorageBackend vyperAbiOperand vyperTyping vyperEncodeDecode
Libs
  wordsLib

val _ = Parse.hide "base";

Definition abi_cell_typed_def:
  abi_cell_typed mem off tv <=>
    ?v. decode_value mem off tv = SOME v /\ value_has_type tv v
End

Definition abi_operand_typed_def:
  abi_operand_typed cx st tv (AbiSnapshot v) = value_has_type tv v /\
  abi_operand_typed cx st tv (AbiMemory token off t) =
    (t = tv /\ ?key mem. oEL token st.abi_memory = SOME (key,mem) /\
                         abi_cell_typed mem off tv) /\
  abi_operand_typed cx st tv (AbiImmutable token off t) =
    (t = tv /\ ?key mem. oEL token st.abi_immutables = SOME (key,mem) /\
                         abi_cell_typed mem off tv) /\
  abi_operand_typed cx st tv (AbiStorage tr slot t) =
    (t = tv /\ abi_cell_typed (get_storage cx st tr) (w2n slot) tv) /\
  abi_operand_typed cx st tv (AbiMapping tr slot kt vt) = F
End

Theorem read_abi_operand_typed:
  abi_operand_typed cx st tv arg ==>
  ?v. read_abi_operand cx arg st = (INL v,st) /\ value_has_type tv v
Proof
  Cases_on `arg` >>
  rw[abi_operand_typed_def, abi_cell_typed_def, read_abi_operand_def,
     read_storage_slot_eq, lift_option_def, return_def] >>
  gvs[return_def] >> metis_tac[]
QED

Theorem read_abi_operand_state:
  read_abi_operand cx arg st = (res,rt) ==> rt = st
Proof
  Cases_on `arg` >>
  rw[read_abi_operand_def, read_storage_slot_eq, lift_option_def,
     return_def, raise_def, AllCaseEqs()] >>
  gvs[option_CASE_rator, AllCaseEqs(), return_def, raise_def]
QED

Theorem unwrap_abi_operand_typed:
  abi_operand_typed cx st tv arg ==>
  ?out. unwrap_abi_operand cx arg st = (INL out,st) /\
        abi_operand_typed cx st tv out
Proof
  strip_tac >> drule read_abi_operand_typed >> strip_tac >>
  Cases_on `arg`
  >- gvs[unwrap_abi_operand_def, return_def, abi_operand_typed_def]
  >- (rename1 `AbiMemory token off t` >> Cases_on `abi_primitive t` >>
      gvs[unwrap_abi_operand_def, bind_def, return_def, abi_operand_typed_def])
  >> gvs[unwrap_abi_operand_def, bind_def, return_def, abi_operand_typed_def,
         read_abi_operand_def]
QED

Theorem unwrap_abi_operand_state:
  unwrap_abi_operand cx arg st = (res,rt) ==> rt = st
Proof
  Cases_on `arg` >>
  rw[unwrap_abi_operand_def, bind_def, return_def, raise_def,
     read_storage_slot_eq, AllCaseEqs()] >>
  imp_res_tac read_abi_operand_state >> gvs[]
QED

Theorem stage_abi_operands_typed:
  !args tvs cx st.
    LIST_REL (abi_operand_typed cx st) tvs args ==>
    ?vs. stage_abi_operands cx args st = (INL vs,st) /\
         LIST_REL value_has_type tvs vs
Proof
  Induct >> Cases_on `tvs` >> simp[stage_abi_operands_def, return_def] >>
  rpt strip_tac >> drule read_abi_operand_typed >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  simp[stage_abi_operands_def, bind_def, return_def] >>
  goal_assum drule >> simp[]
QED

Theorem capture_abi_memory_typed:
  value_has_type tv v /\ well_formed_type_value tv ==>
  ?rt. capture_abi_memory cx id tv v st = (INL (LENGTH st.abi_memory),rt) /\
       abi_operand_typed cx rt tv (AbiMemory (LENGTH st.abi_memory) 0 tv)
Proof
  strip_tac >>
  `?writes. encode_value tv v = SOME writes` by
    metis_tac[value_has_type_equiv, optionTheory.IS_SOME_EXISTS] >>
  drule_all encode_decode_roundtrip_all >>
  simp[encode_decode_roundtrip_ok_def] >> strip_tac >>
  simp[capture_abi_memory_def, return_def, abi_operand_typed_def,
       abi_cell_typed_def, oEL_THM, EL_APPEND_EQN] >>
  metis_tac[]
QED

Theorem capture_abi_immutable_typed:
  value_has_type tv v /\ well_formed_type_value tv ==>
  ?rt. capture_abi_immutable cx src id tv v st =
         (INL (LENGTH st.abi_immutables),rt) /\
       abi_operand_typed cx rt tv (AbiImmutable (LENGTH st.abi_immutables) 0 tv)
Proof
  strip_tac >>
  `?writes. encode_value tv v = SOME writes` by
    metis_tac[value_has_type_equiv, optionTheory.IS_SOME_EXISTS] >>
  drule_all encode_decode_roundtrip_all >>
  simp[encode_decode_roundtrip_ok_def] >> strip_tac >>
  simp[capture_abi_immutable_def, return_def, abi_operand_typed_def,
       abi_cell_typed_def, oEL_THM, EL_APPEND_EQN] >>
  metis_tac[]
QED

Theorem get_storage_abi_immutables[simp]:
  get_storage cx (st with abi_immutables := mem) tr = get_storage cx st tr
Proof
  Cases_on `tr` >> simp[get_storage_def]
QED

Theorem get_storage_abi_memory[simp]:
  get_storage cx (st with abi_memory := mem) tr = get_storage cx st tr
Proof
  Cases_on `tr` >> simp[get_storage_def]
QED

(* Capturing a fresh backing store cannot invalidate an older raw reference. *)
Theorem abi_operand_typed_capture_frame:
  abi_operand_typed cx st tv arg /\
  capture_abi_memory cxf id t v st = (res,rt) ==>
  abi_operand_typed cx rt tv arg
Proof
  Cases_on `arg` >>
  rw[capture_abi_memory_def, AllCaseEqs(), return_def, raise_def] >>
  gvs[abi_operand_typed_def] >>
  gvs[oEL_THM, EL_APPEND_EQN, get_storage_def] >>
  metis_tac[]
QED

Theorem abi_operand_typed_capture_immutable_frame:
  abi_operand_typed cx st tv arg /\
  capture_abi_immutable cxf src id t v st = (res,rt) ==>
  abi_operand_typed cx rt tv arg
Proof
  Cases_on `arg` >>
  rw[capture_abi_immutable_def, AllCaseEqs(), return_def, raise_def] >>
  gvs[abi_operand_typed_def] >>
  gvs[oEL_THM, EL_APPEND_EQN, get_storage_def] >>
  metis_tac[]
QED

Theorem abi_immutable_typed_release:
  abi_operand_typed cx st tv (AbiImmutable token off tv) ==>
  abi_operand_typed cx (SND (release_abi_memory mark st)) tv
    (AbiImmutable token off tv)
Proof
  simp[abi_operand_typed_def, release_abi_memory_def, return_def]
QED

(* The token bound here is an arena-lifetime bound, not an array index bound. *)
Theorem abi_memory_typed_release:
  abi_operand_typed cx st tv (AbiMemory token off tv) /\ token < mark ==>
  abi_operand_typed cx (SND (release_abi_memory mark st)) tv
    (AbiMemory token off tv)
Proof
  rw[abi_operand_typed_def, release_abi_memory_def, return_def] >>
  gvs[oEL_THM, EL_TAKE, LENGTH_TAKE_EQ, MIN_DEF] >> decide_tac
QED

Theorem abi_cell_typed_disjoint_writes:
  !(mem:storage) (off:num) tv (base:num) (sz:num) writes.
  abi_cell_typed mem off tv /\
  (!k. MEM k (MAP FST writes) ==> k < sz) /\
  base + sz <= dimword(:256) /\ off + type_slot_size tv <= dimword(:256) /\
  (base + sz <= off \/ off + type_slot_size tv <= base) ==>
  abi_cell_typed (apply_writes (n2w base) writes mem) off tv
Proof
  rpt gen_tac >> strip_tac >>
  `decode_value (apply_writes (n2w base) writes mem) off tv =
   decode_value mem off tv` by
    (irule decode_value_disjoint_writes >> fs[] >>
     qexists_tac `sz` >> fs[]) >>
  gvs[abi_cell_typed_def]
QED

(* Pop changes the length word only. This applies to complex popped cells at
   their old addresses, without asking that they are still in logical bounds. *)
Theorem abi_cell_typed_pop_length:
  abi_cell_typed mem off tv /\ base + 1 <= off /\
  off + type_slot_size tv <= dimword(:256) ==>
  abi_cell_typed (apply_writes (n2w base) [(0,n2w len)] mem) off tv
Proof
  strip_tac >> irule abi_cell_typed_disjoint_writes >>
  fs[] >> qexists_tac `1` >> fs[] >> decide_tac
QED

(* Actual local alias-store write, over every token and every cell type. The
   offset is an already captured address; no later logical-length test occurs. *)
Theorem write_abi_memory_pop_preserves_cell:
  !cx st tv token off id elem cap vs res rt.
  abi_operand_typed cx st tv (AbiMemory token off tv) /\
  1 <= off /\ off + type_slot_size tv <= dimword(:256) /\
  write_abi_memory cx id (ArrayTV elem (Dynamic cap))
    (ArrayV (DynArrayV vs)) [] PopOp st = (res,rt) ==>
  res = INL () /\ abi_operand_typed cx rt tv (AbiMemory token off tv)
Proof
  rpt gen_tac >>
  rw[write_abi_memory_def, abi_path_offset_def, evaluate_subscripts_def,
     abi_operation_writes_def, return_def] >>
  gvs[abi_operand_typed_def, oEL_THM, EL_MAP] >>
  rw[] >> irule abi_cell_typed_pop_length >> simp[]
QED

(* The same preservation fact at an arbitrary captured path. The hypotheses
   describe the writer's actual footprint, never a current logical index bound
   on the outstanding operand. This also covers aliases of nested arrays. *)
Theorem write_abi_memory_disjoint_preserves_cell:
  !cx st tv token off id root v subs ao base child_tv child writes sz res rt.
  abi_operand_typed cx st tv (AbiMemory token off tv) /\
  abi_path_offset root subs = SOME (base,child_tv) /\
  evaluate_subscripts root v subs = INL child /\
  abi_operation_writes child_tv child ao = SOME writes /\
  (!k. MEM k (MAP FST writes) ==> k < sz) /\
  base + sz <= dimword(:256) /\
  off + type_slot_size tv <= dimword(:256) /\
  (base + sz <= off \/ off + type_slot_size tv <= base) /\
  write_abi_memory cx id root v subs ao st = (res,rt) ==>
  res = INL () /\ abi_operand_typed cx rt tv (AbiMemory token off tv)
Proof
  rpt gen_tac >>
  rw[write_abi_memory_def, return_def] >>
  gvs[abi_operand_typed_def, oEL_THM, EL_MAP] >>
  rw[] >> irule abi_cell_typed_disjoint_writes >> simp[] >>
  qexists_tac `sz` >> simp[]
QED

Theorem write_abi_memory_preserves_immutable_cell:
  abi_operand_typed cx st tv (AbiImmutable token off tv) /\
  write_abi_memory cxf id root v subs ao st = (res,rt) ==>
  abi_operand_typed cx rt tv (AbiImmutable token off tv)
Proof
  rw[write_abi_memory_def, AllCaseEqs(), return_def, raise_def] >>
  gvs[AllCaseEqs(), return_def, raise_def, abi_operand_typed_def]
QED

Theorem write_abi_immutables_preserves_memory_cell:
  abi_operand_typed cx st tv (AbiMemory token off tv) /\
  write_abi_immutables cxf src id root v subs ao st = (res,rt) ==>
  abi_operand_typed cx rt tv (AbiMemory token off tv)
Proof
  rw[write_abi_immutables_def, AllCaseEqs(), return_def, raise_def] >>
  gvs[AllCaseEqs(), return_def, raise_def, abi_operand_typed_def]
QED

(* Immutable writes use the same physical footprint in the separate arena.
   Outstanding popped pointers remain typed even beyond logical length. *)
Theorem write_abi_immutables_disjoint_preserves_cell:
  !cx st tv token off src id root v subs ao base child_tv child writes sz res rt.
  abi_operand_typed cx st tv (AbiImmutable token off tv) /\
  abi_path_offset root subs = SOME (base,child_tv) /\
  evaluate_subscripts root v subs = INL child /\
  abi_operation_writes child_tv child ao = SOME writes /\
  (!k. MEM k (MAP FST writes) ==> k < sz) /\
  base + sz <= dimword(:256) /\
  off + type_slot_size tv <= dimword(:256) /\
  (base + sz <= off \/ off + type_slot_size tv <= base) /\
  write_abi_immutables cx src id root v subs ao st = (res,rt) ==>
  res = INL () /\ abi_operand_typed cx rt tv (AbiImmutable token off tv)
Proof
  rpt gen_tac >>
  rw[write_abi_immutables_def, return_def] >>
  gvs[abi_operand_typed_def, oEL_THM, EL_MAP] >>
  rw[] >> irule abi_cell_typed_disjoint_writes >> simp[] >>
  qexists_tac `sz` >> simp[]
QED

Theorem write_abi_immutables_pop_preserves_cell:
  !cx st tv token off src id elem cap vs res rt.
  abi_operand_typed cx st tv (AbiImmutable token off tv) /\
  1 <= off /\ off + type_slot_size tv <= dimword(:256) /\
  write_abi_immutables cx src id (ArrayTV elem (Dynamic cap))
    (ArrayV (DynArrayV vs)) [] PopOp st = (res,rt) ==>
  res = INL () /\ abi_operand_typed cx rt tv (AbiImmutable token off tv)
Proof
  rpt gen_tac >>
  rw[write_abi_immutables_def, abi_path_offset_def, evaluate_subscripts_def,
     abi_operation_writes_def, return_def] >>
  gvs[abi_operand_typed_def, oEL_THM, EL_MAP] >>
  rw[] >> irule abi_cell_typed_pop_length >> simp[]
QED

Theorem write_abi_immutables_pop_path_preserves_cell:
  !cx st tv token off src id root v subs base elem cap vs res rt.
  abi_operand_typed cx st tv (AbiImmutable token off tv) /\
  abi_path_offset root subs = SOME (base,ArrayTV elem (Dynamic cap)) /\
  evaluate_subscripts root v subs = INL (ArrayV (DynArrayV vs)) /\
  base + 1 <= off /\ off + type_slot_size tv <= dimword(:256) /\
  write_abi_immutables cx src id root v subs PopOp st = (res,rt) ==>
  res = INL () /\ abi_operand_typed cx rt tv (AbiImmutable token off tv)
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`cx`, `st`, `tv`, `token`, `off`, `src`, `id`, `root`, `v`,
    `subs`, `PopOp`, `base`, `ArrayTV elem (Dynamic cap)`,
    `ArrayV (DynArrayV vs)`, `[(0,n2w (LENGTH vs))]`, `1`, `res`, `rt`]
    mp_tac write_abi_immutables_disjoint_preserves_cell >>
  simp[abi_operation_writes_def] >>
  disch_then irule >> fs[] >> decide_tac
QED

Theorem write_abi_memory_pop_path_preserves_cell:
  !cx st tv token off id root v subs base elem cap vs res rt.
  abi_operand_typed cx st tv (AbiMemory token off tv) /\
  abi_path_offset root subs = SOME (base,ArrayTV elem (Dynamic cap)) /\
  evaluate_subscripts root v subs = INL (ArrayV (DynArrayV vs)) /\
  base + 1 <= off /\ off + type_slot_size tv <= dimword(:256) /\
  write_abi_memory cx id root v subs PopOp st = (res,rt) ==>
  res = INL () /\ abi_operand_typed cx rt tv (AbiMemory token off tv)
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`cx`, `st`, `tv`, `token`, `off`, `id`, `root`, `v`,
    `subs`, `PopOp`, `base`, `ArrayTV elem (Dynamic cap)`,
    `ArrayV (DynArrayV vs)`, `[(0,n2w (LENGTH vs))]`, `1`, `res`, `rt`]
    mp_tac write_abi_memory_disjoint_preserves_cell >>
  simp[abi_operation_writes_def] >>
  disch_then irule >> fs[] >> decide_tac
QED
