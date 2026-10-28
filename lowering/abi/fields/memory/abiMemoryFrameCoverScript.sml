(* TOP-LEVEL: replace individual write windows by covering resource arenas
   and compose repeated writes within the same arenas across loop iterations. *)
Theory abiMemoryFrameCover
Ancestors abiMemoryFrame compileEnv venomState list pair arithmetic

Definition abi_writes_cover_def:
  abi_writes_cover outer inner <=>
    !base write_len. MEM (base,write_len) inner ==>
      ?arena capacity. MEM (arena,capacity) outer /\ arena <= base /\ base + write_len <= arena + capacity
End

Theorem abi_writes_cover_separated:
  !outer inner offset read_len.
    abi_writes_cover outer inner /\
    EVERY (\(base,write_len). abi_window_separated offset read_len base write_len) outer ==>
    EVERY (\(base,write_len). abi_window_separated offset read_len base write_len) inner
Proof
  rpt gen_tac >> simp_tac (srw_ss()) [abi_writes_cover_def, EVERY_MEM, FORALL_PROD] >> strip_tac >>
  MAP_EVERY qx_gen_tac [`write_base`, `write_count`] >> DISCH_TAC >>
  qpat_x_assum `!base write_len. MEM _ inner ==> _` (qspecl_then [`write_base`, `write_count`] mp_tac) >>
  impl_tac >- first_assum MATCH_ACCEPT_TAC >>
  disch_then (qx_choose_then `arena` (qx_choose_then `capacity` strip_assume_tac)) >>
  mp_tac (Q.SPECL [`offset`, `read_len`, `arena`, `capacity`, `write_base`, `write_count`] abi_window_separated_subwindow) >>
  impl_tac >- (simp[] >> qpat_x_assum `!base write_len. MEM _ outer ==> _`
    (qspecl_then [`arena`, `capacity`] mp_tac) >> simp[]) >> simp[]
QED

Theorem abi_memory_frame_cover:
  !outer inner before after.
    abi_writes_cover outer inner /\ abi_memory_frame inner before after ==>
    abi_memory_frame outer before after
Proof
  rpt gen_tac >> strip_tac >> simp_tac bool_ss [abi_memory_frame_def] >>
  MAP_EVERY qx_gen_tac [`offset`, `read_len`] >> DISCH_TAC >>
  mp_tac (Q.SPECL [`outer`, `inner`, `offset`, `read_len`] abi_writes_cover_separated) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> DISCH_TAC >>
  irule abi_memory_frame_read >> qexists_tac `inner` >> simp[]
QED

Theorem abi_memory_frame_trans_same:
  !writes before mid after.
    abi_memory_frame writes before mid /\ abi_memory_frame writes mid after ==>
    abi_memory_frame writes before after
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`writes`, `writes`, `before`, `mid`, `after`] abi_memory_frame_trans) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  simp[abi_memory_frame_def, EVERY_APPEND]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed covering ABI resource frames: " ^ name)
  end) (DB.thms "abiMemoryFrameCover")
