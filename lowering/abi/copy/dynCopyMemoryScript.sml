(* TOP-LEVEL: copying a dynamic array's live prefix establishes the entire
   typed destination layout. Unused capacity is unrestricted. Zero-size
   elements and empty arrays are included; payload windows may overlap. *)
Theory dynCopyMemory
Ancestors
  dynCopyExec memoryValueDefs memoryValueRelocation memoryValueFrame
  memoryReadProps valueEncoding valueEncodingProps venomState venomExecSemantics
  venomMemProps list words arithmetic

Definition dyn_copy_memory_def:
  dyn_copy_memory dst src n elem_size ss =
    mcopy (dst + 32) (src + 32) (n * elem_size) (mstore dst (n2w n) ss)
End

Theorem dyn_copy_memory_header:
  !dst src n elem_size ss.
    mload dst (dyn_copy_memory dst src n elem_size ss) = n2w n
Proof
  rpt gen_tac >>
  `mload dst (dyn_copy_memory dst src n elem_size ss) = mload dst (mstore dst (n2w n) ss)` by
    (PURE_REWRITE_TAC [mload_read_memory, dyn_copy_memory_def] >>
     AP_TERM_TAC >> irule read_memory_mcopy_disjoint >> simp[]) >>
  simp[mload_mstore_same]
QED

Theorem dyn_copy_memory_payload:
  !dst src n elem_size ss.
    n * elem_size = 0 \/ src + 32 + n * elem_size <= dst \/ dst <= src ==>
    read_memory (dst + 32) (n * elem_size) (dyn_copy_memory dst src n elem_size ss) =
      read_memory (src + 32) (n * elem_size) ss
Proof
  rpt gen_tac >> DISCH_TAC >> Cases_on `n * elem_size = 0`
  >- simp[read_memory_def] >>
  PURE_REWRITE_TAC [dyn_copy_memory_def, read_memory_mcopy_self] >>
  irule read_memory_mstore_disjoint >> fs[] >> decide_tac
QED

Theorem copy_relative_window:
  !src dst whole_len skip read_len (ss:venom_state) (out:venom_state).
    read_memory src whole_len ss = read_memory dst whole_len out /\
    skip + read_len <= whole_len ==>
    mem_bytes_at (src + skip) read_len ss.vs_memory =
      mem_bytes_at (dst + skip) read_len out.vs_memory
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`src`, `whole_len`, `skip`, `read_len`, `ss`] read_memory_subwindow) >>
  mp_tac (Q.SPECL [`dst`, `whole_len`, `skip`, `read_len`, `out`] read_memory_subwindow) >>
  simp[read_memory_eq_mem_bytes_at]
QED

Theorem array_copy_slot_bound:
  !i n elem_size. i < n ==> i * elem_size + elem_size <= n * elem_size
Proof
  rpt strip_tac >> `i + 1 <= n` by decide_tac >>
  `i * elem_size + elem_size = (i + 1) * elem_size` by simp[RIGHT_ADD_DISTRIB] >>
  asm_rewrite_tac [] >> simp[LE_MULT_RCANCEL]
QED

Theorem dyn_copy_memory_element:
  !tv vs src_capacity dst src ss i.
    memory_value_rel (ArrayTV tv (Dynamic src_capacity)) (ArrayV (DynArrayV vs)) src ss.vs_memory /\
    EVERY (val_wf tv) vs /\ i < LENGTH vs /\
    (LENGTH vs * type_memory_size tv = 0 \/
      src + 32 + LENGTH vs * type_memory_size tv <= dst \/ dst <= src) ==>
    memory_value_rel tv (EL i vs) (dst + 32 + i * type_memory_size tv)
      (dyn_copy_memory dst src (LENGTH vs) (type_memory_size tv) ss).vs_memory
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  `val_wf tv (EL i vs)` by fs[EVERY_EL] >>
  `read_memory (dst + 32) (LENGTH vs * type_memory_size tv)
     (dyn_copy_memory dst src (LENGTH vs) (type_memory_size tv) ss) =
    read_memory (src + 32) (LENGTH vs * type_memory_size tv) ss` by
    (irule dyn_copy_memory_payload >> first_assum ACCEPT_TAC) >>
  `memory_value_rel tv (EL i vs) (src + 32 + i * type_memory_size tv) ss.vs_memory` by
    (qpat_x_assum `memory_value_rel (ArrayTV _ _) _ _ _` mp_tac >>
     simp_tac bool_ss [Once memory_value_rel_def] >> strip_tac >> first_x_assum irule >> simp[]) >>
  mp_tac (Q.SPECL [`src + 32`, `dst + 32`, `LENGTH (vs:value list) * type_memory_size tv`,
    `i * type_memory_size tv`, `type_memory_size tv`, `ss`,
    `dyn_copy_memory dst src (LENGTH (vs:value list)) (type_memory_size tv) ss`] copy_relative_window) >>
  impl_tac >- (conj_tac >- simp[] >> irule array_copy_slot_bound >> simp[]) >> DISCH_TAC >>
  mp_tac (Q.SPECL [`tv`, `EL i (vs:value list)`, `src + 32 + i * type_memory_size tv`,
    `ss.vs_memory`, `dst + 32 + i * type_memory_size tv`,
    `(dyn_copy_memory dst src (LENGTH (vs:value list)) (type_memory_size tv) ss).vs_memory`]
    memory_value_rel_relocate) >> simp[EVERY_EL]
QED

Theorem dyn_copy_memory_layout:
  !tv vs src_capacity dst_capacity dst src ss.
    memory_value_rel (ArrayTV tv (Dynamic src_capacity)) (ArrayV (DynArrayV vs)) src ss.vs_memory /\
    EVERY (val_wf tv) vs /\
    (LENGTH vs * type_memory_size tv = 0 \/
      src + 32 + LENGTH vs * type_memory_size tv <= dst \/ dst <= src) ==>
    memory_value_rel (ArrayTV tv (Dynamic dst_capacity)) (ArrayV (DynArrayV vs)) dst
      (dyn_copy_memory dst src (LENGTH vs) (type_memory_size tv) ss).vs_memory
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  simp_tac bool_ss [Once memory_value_rel_def] >> conj_tac
  >- simp[mem_word_at_eq_mload, dyn_copy_memory_header] >>
  qx_gen_tac `i` >> DISCH_TAC >>
  mp_tac (Q.SPECL [`tv`, `vs`, `src_capacity`, `dst`, `src`, `ss`, `i`]
    dyn_copy_memory_element) >> simp[]
QED

Theorem dyn_copy_result_natural_memory:
  !var_base elem_size dst_addr src_addr n ss.
    w2n (dst_addr:bytes32) + 32 < dimword(:256) /\
    w2n (src_addr:bytes32) + 32 < dimword(:256) /\ n * elem_size < dimword(:256) ==>
    (dyn_copy_result var_base elem_size dst_addr src_addr n ss).vs_memory =
      (dyn_copy_memory (w2n dst_addr) (w2n src_addr) n elem_size ss).vs_memory
Proof
  rpt gen_tac >> Cases_on `dst_addr` >> Cases_on `src_addr` >>
  simp[dyn_copy_result_memory, dyn_copy_memory_def, word_add_n2w, word_mul_n2w] >>
  rpt strip_tac >> simp[]
QED

Theorem dyn_copy_result_layout:
  !tv vs src_capacity dst_capacity var_base dst_addr src_addr ss.
    memory_value_rel (ArrayTV tv (Dynamic src_capacity)) (ArrayV (DynArrayV vs))
      (w2n src_addr) ss.vs_memory /\ EVERY (val_wf tv) vs /\
    w2n (dst_addr:bytes32) + 32 < dimword(:256) /\
    w2n (src_addr:bytes32) + 32 < dimword(:256) /\
    LENGTH vs * type_memory_size tv < dimword(:256) /\
    (LENGTH vs * type_memory_size tv = 0 \/
      w2n src_addr + 32 + LENGTH vs * type_memory_size tv <= w2n dst_addr \/
      w2n dst_addr <= w2n src_addr) ==>
    memory_value_rel (ArrayTV tv (Dynamic dst_capacity)) (ArrayV (DynArrayV vs))
      (w2n dst_addr) (dyn_copy_result var_base (type_memory_size tv)
        dst_addr src_addr (LENGTH vs) ss).vs_memory
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  mp_tac (Q.SPECL [`var_base`, `type_memory_size tv`, `dst_addr`, `src_addr`,
    `LENGTH (vs:value list)`, `ss`] dyn_copy_result_natural_memory) >>
  impl_tac >- simp[] >> DISCH_TAC >> asm_rewrite_tac [] >>
  mp_tac (Q.SPECL [`tv`, `vs`, `src_capacity`, `dst_capacity`, `w2n (dst_addr:bytes32)`,
    `w2n (src_addr:bytes32)`, `ss`] dyn_copy_memory_layout) >> simp[]
QED

Theorem dyn_copy_memory_preserves_value:
  !tv v offset dst src n elem_size ss.
    memory_value_rel tv v offset ss.vs_memory /\ val_wf tv v /\
    (offset + type_memory_size tv <= dst \/ dst + 32 + n * elem_size <= offset) ==>
    memory_value_rel tv v offset (dyn_copy_memory dst src n elem_size ss).vs_memory
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) >>
  `memory_value_rel tv v offset (mstore dst (n2w n) ss).vs_memory` by
    (irule mstore_preserves_memory_value_rel >> simp[] >> decide_tac) >>
  PURE_REWRITE_TAC [dyn_copy_memory_def] >> irule mcopy_preserves_memory_value_rel >>
  simp[] >> decide_tac
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed dynamic-array copy layout theorem: " ^ name)
  end) (DB.thms "dynCopyMemory")
