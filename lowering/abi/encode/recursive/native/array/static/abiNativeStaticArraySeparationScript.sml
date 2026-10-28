(* TOP-LEVEL: allocation identities separate a static iteration's data and
   counter writes from the entire source, output header and packed prefix.
   Reads sharing the target allocation use their adjacent numeric windows. *)
Theory abiNativeStaticArraySeparation
Ancestors
  abiAllocatedWindows abiAllocatedSubwindows abiAllocatedSeparation abiMemoryFrame
  compileEnv venomMemDefs venomState list pair words arithmetic

Theorem abi_native_static_array_owned:
  !ss target_id dst_base payload_len index width.
    abi_allocated_window ss target_id dst_base payload_len /\
    32 + index * width + width <= payload_len ==>
    abi_allocated_window ss target_id dst_base 32 /\
    abi_allocated_window ss target_id (dst_base + 32) (index * width) /\
    abi_allocated_window ss target_id (dst_base + 32 + index * width) width
Proof
  rpt gen_tac >> strip_tac >>
  `abi_allocated_window ss target_id dst_base 32` by
    (qspecl_then [`ss`, `target_id`, `dst_base`, `payload_len`, `32`]
       mp_tac abi_allocated_window_shrink >> impl_tac >- (asm_simp_tac bool_ss [] >> decide_tac) >> simp[]) >>
  `abi_allocated_window ss target_id (dst_base + 32) (index * width)` by
    (qspecl_then [`ss`, `target_id`, `dst_base`, `payload_len`, `dst_base + 32`, `index * width`]
       mp_tac abi_allocated_window_subwindow >> impl_tac >- (asm_simp_tac bool_ss [] >> decide_tac) >> simp[]) >>
  `abi_allocated_window ss target_id (dst_base + 32 + index * width) width` by
    (qspecl_then [`ss`, `target_id`, `dst_base`, `payload_len`, `dst_base + 32 + index * width`, `width`]
       mp_tac abi_allocated_window_subwindow >> impl_tac >- (asm_simp_tac bool_ss [] >> decide_tac) >> simp[]) >>
  rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

Theorem abi_native_static_array_writes_separated:
  !ss source_id target_id counter_id source_base source_capacity dst_base payload_len counter_base index width.
    allocas_non_overlapping ss /\ source_id <> target_id /\ counter_id <> source_id /\ counter_id <> target_id /\
    abi_allocated_window ss source_id source_base source_capacity /\
    abi_allocated_window ss target_id dst_base payload_len /\ abi_allocated_window ss counter_id counter_base 32 /\
    32 + index * width + width <= payload_len ==>
    EVERY (\(b,n). abi_window_separated source_base source_capacity b n)
      [(dst_base + 32 + index * width,width);(counter_base,32)] /\
    EVERY (\(b,n). abi_window_separated dst_base 32 b n)
      [(dst_base + 32 + index * width,width);(counter_base,32)] /\
    EVERY (\(b,n). abi_window_separated (dst_base + 32) (index * width) b n)
      [(dst_base + 32 + index * width,width);(counter_base,32)] /\
    abi_window_separated (dst_base + 32 + index * width) width counter_base 32
Proof
  rpt gen_tac >> strip_tac >> drule_all abi_native_static_array_owned >> strip_tac >>
  `abi_window_separated dst_base 32 (dst_base + 32 + index * width) width /\
    abi_window_separated (dst_base + 32) (index * width) (dst_base + 32 + index * width) width` by
    simp[abi_window_separated_def, compileEnvTheory.regions_disjoint_def] >>
  qspecl_then [`ss`, `[(target_id,(dst_base + 32 + index * width,width));(counter_id,(counter_base,32))]`,
    `source_id`, `source_base`, `source_capacity`] mp_tac abi_allocated_windows_separated >>
  impl_tac >- asm_simp_tac bool_ss [EVERY_DEF, FST, SND, EQ_SYM_EQ] >> simp_tac bool_ss [MAP, SND] >> DISCH_TAC >>
  qspecl_then [`ss`, `[(target_id,(dst_base + 32 + index * width,width));(counter_id,(counter_base,32))]`,
    `target_id`, `dst_base`, `32`] mp_tac abi_allocated_windows_separated >>
  impl_tac >- asm_simp_tac bool_ss [EVERY_DEF, FST, SND, EQ_SYM_EQ] >> simp_tac bool_ss [MAP, SND] >> DISCH_TAC >>
  qspecl_then [`ss`, `[(target_id,(dst_base + 32 + index * width,width));(counter_id,(counter_base,32))]`,
    `target_id`, `dst_base + 32`, `index * width`] mp_tac abi_allocated_windows_separated >>
  impl_tac >- asm_simp_tac bool_ss [EVERY_DEF, FST, SND, EQ_SYM_EQ] >> simp_tac bool_ss [MAP, SND] >> DISCH_TAC >>
  qspecl_then [`ss`, `target_id`, `dst_base + 32 + index * width`, `width`, `counter_id`, `counter_base`, `32`]
    mp_tac abi_allocated_window_separated >> impl_tac >- asm_simp_tac bool_ss [EQ_SYM_EQ] >> DISCH_TAC >>
  rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed owned static runtime iteration separation: " ^ name)
  end) (DB.thms "abiNativeStaticArraySeparation")
