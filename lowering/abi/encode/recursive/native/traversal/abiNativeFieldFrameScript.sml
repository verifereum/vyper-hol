(* TOP-LEVEL: an actual field's data, local scratch profile and parent
   stores fit the enclosing payload/profile frame. Extra stores must have
   concrete covering windows, rather than an assumed enclosing run. *)
Theory abiNativeFieldFrame
Ancestors
  abiMemoryLeafRun abiAllocationWindows abiMemoryFrameCover abiMemoryFrame allocationGrowth
  compileAllocaProfiles compileAllocaProvenance compileEnv venomState list pair words arithmetic

Theorem abi_native_field_writes_cover:
  !root_ids local_ids ss root_dst root_payload dst_addr payload extra.
    set local_ids SUBSET set root_ids /\
    w2n (root_dst:bytes32) <= w2n (dst_addr:bytes32) /\
    w2n dst_addr + LENGTH (payload:word8 list) <= w2n root_dst + LENGTH (root_payload:word8 list) /\
    abi_writes_cover ((w2n root_dst,LENGTH root_payload)::abi_allocation_windows root_ids ss) extra ==>
    abi_writes_cover ((w2n root_dst,LENGTH root_payload)::abi_allocation_windows root_ids ss)
      ((w2n dst_addr,LENGTH payload)::(abi_allocation_windows local_ids ss ++ extra))
Proof
  rpt gen_tac >> strip_tac >> simp_tac bool_ss [abi_writes_cover_def, MEM, MEM_APPEND] >>
  MAP_EVERY qx_gen_tac [`write_base`, `write_count`] >> strip_tac
  >| [gvs[] >> qexistsl_tac [`w2n root_dst`, `LENGTH root_payload`] >> simp[],
      qexistsl_tac [`write_base`, `write_count`] >> simp[] >> disj2_tac >>
        qspecl_then [`ss`, `ss`, `local_ids`, `root_ids`, `(write_base,write_count)`]
          mp_tac abi_allocation_windows_growth >> simp[],
      qpat_x_assum `abi_writes_cover _ extra`
        (mp_tac o PURE_REWRITE_RULE [abi_writes_cover_def]) >>
        disch_then (qspecl_then [`write_base`, `write_count`] mp_tac) >> simp[]]
QED

Theorem abi_native_field_frame:
  !ctx func root_cs root_after root_dst root_payload cs mid ret dst_addr payload extra ss out.
    abi_encoding_result ctx func cs mid ret (dst_addr:bytes32) payload
      (abi_allocation_windows (compiler_alloca_ids cs mid) out ++ extra) ss out /\
    cs_extends root_cs cs /\ cs_extends mid root_after /\
    w2n (root_dst:bytes32) <= w2n dst_addr /\
    w2n dst_addr + LENGTH payload <= w2n root_dst + LENGTH (root_payload:word8 list) /\
    abi_writes_cover ((w2n root_dst,LENGTH root_payload)::
      abi_allocation_windows (compiler_alloca_ids root_cs root_after) out) extra ==>
    abi_memory_frame ((w2n root_dst,LENGTH root_payload)::
      abi_allocation_windows (compiler_alloca_ids root_cs root_after) out) ss out
Proof
  rpt gen_tac >> strip_tac >>
  `set (compiler_alloca_ids cs mid) SUBSET set (compiler_alloca_ids root_cs root_after)` by
    (irule compiler_alloca_profile_subprofile >> simp[]) >>
  qpat_x_assum `abi_encoding_result _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [abi_encoding_result_def]) >>
  irule abi_memory_frame_cover >>
  qexists_tac `(w2n dst_addr,LENGTH payload)::
    (abi_allocation_windows (compiler_alloca_ids cs mid) out ++ extra)` >>
  conj_tac >- (
    qspecl_then [`compiler_alloca_ids root_cs root_after`, `compiler_alloca_ids cs mid`, `out`,
      `root_dst`, `root_payload`, `dst_addr`, `payload`, `extra`] mp_tac abi_native_field_writes_cover >>
    impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> simp[]) >>
  first_assum MATCH_ACCEPT_TAC
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed actual enclosing field write frames: " ^ name)
  end) (DB.thms "abiNativeFieldFrame")
