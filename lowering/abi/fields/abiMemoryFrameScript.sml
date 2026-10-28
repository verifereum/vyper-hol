(* TOP-LEVEL: memory frames describe all written windows, including nested
   encoder scratch cells. Empty windows impose no separation requirement.
   These frames compose across fields without claiming scratch writes occur
   only in the output buffer. *)
Theory abiMemoryFrame
Ancestors
  memoryReadProps compileEnv venomState venomExecSemantics list pair arithmetic

Definition abi_window_separated_def:
  abi_window_separated offset read_len base write_len <=>
    read_len = 0 \/ write_len = 0 \/ regions_disjoint offset read_len base write_len
End

Definition abi_memory_frame_def:
  abi_memory_frame writes (before:venom_state) (after:venom_state) <=>
    !offset read_len.
      EVERY (\(base,write_len). abi_window_separated offset read_len base write_len) writes ==>
      read_memory offset read_len after = read_memory offset read_len before
End

Theorem abi_window_separated_sym:
  !offset read_len base write_len.
    abi_window_separated offset read_len base write_len =
      abi_window_separated base write_len offset read_len
Proof
  simp[abi_window_separated_def, regions_disjoint_def] >> metis_tac[]
QED

Theorem abi_window_separated_subwindow:
  !offset read_len base write_len sub_base sub_len.
    abi_window_separated offset read_len base write_len /\
    base <= sub_base /\ sub_base + sub_len <= base + write_len ==>
    abi_window_separated offset read_len sub_base sub_len
Proof
  rpt gen_tac >> simp_tac bool_ss [abi_window_separated_def, regions_disjoint_def] >>
  rpt strip_tac >> decide_tac
QED

Theorem abi_memory_frame_refl[simp]:
  !writes ss. abi_memory_frame writes ss ss
Proof
  simp[abi_memory_frame_def]
QED

Theorem abi_memory_frame_memory:
  !writes before after. after.vs_memory = before.vs_memory ==> abi_memory_frame writes before after
Proof
  simp[abi_memory_frame_def, read_memory_def]
QED

Theorem abi_memory_frame_read:
  !writes before after offset read_len.
    abi_memory_frame writes before after /\
    EVERY (\(base,write_len). abi_window_separated offset read_len base write_len) writes ==>
    read_memory offset read_len after = read_memory offset read_len before
Proof
  simp[abi_memory_frame_def]
QED

Theorem abi_memory_frame_append_left:
  !left right before after.
    abi_memory_frame left before after ==> abi_memory_frame (left ++ right) before after
Proof
  simp[abi_memory_frame_def, EVERY_APPEND] >> rpt strip_tac >> first_x_assum irule >> simp[]
QED

Theorem abi_memory_frame_mload:
  !writes before after offset.
    abi_memory_frame writes before after /\
    EVERY (\(base,write_len). abi_window_separated offset 32 base write_len) writes ==>
    mload offset after = mload offset before
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`writes`, `before`, `after`, `offset`, `32`] abi_memory_frame_read) >>
  impl_tac >- (conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  asm_simp_tac bool_ss [mload_read_memory]
QED

Theorem abi_memory_frame_append_right:
  !left right before after.
    abi_memory_frame right before after ==> abi_memory_frame (left ++ right) before after
Proof
  simp[abi_memory_frame_def, EVERY_APPEND] >> rpt strip_tac >> first_x_assum irule >> simp[]
QED

Theorem abi_memory_frame_trans:
  !left right before mid after.
    abi_memory_frame left before mid /\ abi_memory_frame right mid after ==>
    abi_memory_frame (left ++ right) before after
Proof
  rpt gen_tac >> simp_tac bool_ss [abi_memory_frame_def, EVERY_APPEND] >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  irule EQ_TRANS >> qexists_tac `read_memory offset read_len mid` >>
  conj_tac >> first_x_assum irule >> simp[]
QED

Theorem abi_memory_frame_mstore:
  !offset value ss. abi_memory_frame [(offset,32)] ss (mstore offset value ss)
Proof
  rpt gen_tac >> simp_tac (srw_ss()) [abi_memory_frame_def, abi_window_separated_def] >>
  rpt gen_tac >> strip_tac
  >- simp[read_memory_def] >>
  irule read_memory_mstore_disjoint >> fs[regions_disjoint_def]
QED

Theorem abi_memory_frame_mcopy:
  !dst src byte_count ss. abi_memory_frame [(dst,byte_count)] ss (mcopy dst src byte_count ss)
Proof
  rpt gen_tac >> simp_tac (srw_ss()) [abi_memory_frame_def, abi_window_separated_def] >>
  rpt gen_tac >> strip_tac
  >- simp[read_memory_def]
  >- simp[read_memory_mcopy_zero] >>
  irule read_memory_mcopy_frame >> fs[regions_disjoint_def]
QED

Theorem abi_memory_frame_inst_idx:
  !writes before after index.
    abi_memory_frame writes before (after with vs_inst_idx := index) =
      abi_memory_frame writes before after
Proof
  simp[abi_memory_frame_def, read_memory_def]
QED

Theorem abi_memory_frame_update_var:
  !writes before after name value.
    abi_memory_frame writes before (update_var name value after) = abi_memory_frame writes before after
Proof
  simp[abi_memory_frame_def, read_memory_def, update_var_def]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed ABI written-window memory frames: " ^ name)
  end) (DB.thms "abiMemoryFrame")
