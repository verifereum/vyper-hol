(* TOP-LEVEL: live runtime indices select non-wrapping element windows,
   including zero-width strides. The whole arena endpoint is strict. *)
Theory abiNativeArrayBounds
Ancestors
  abiStaticLoopMemory compileEnv venomState words arithmetic

Theorem abi_native_array_index_bounds:
  !addr index loop_count stride.
    index < loop_count /\ w2n (addr:bytes32) + 32 + loop_count * stride < dimword (:256) ==>
    w2n addr + 32 + index * stride < dimword (:256) /\
    w2n addr + 32 + index * stride + stride <= w2n addr + 32 + loop_count * stride /\
    w2n (addr + 32w + n2w index * n2w stride) = w2n addr + 32 + index * stride
Proof
  rpt gen_tac >> strip_tac >>
  `index * stride <= loop_count * stride` by (simp[LE_MULT_RCANCEL] >> decide_tac) >>
  `(index + 1) * stride <= loop_count * stride` by (simp[LE_MULT_RCANCEL] >> decide_tac) >>
  `w2n addr + 32 + index * stride < dimword (:256) /\
    w2n addr + 32 + index * stride + stride <= w2n addr + 32 + loop_count * stride` by
    (qpat_x_assum `(index + 1) * stride <= loop_count * stride`
       (mp_tac o PURE_REWRITE_RULE [RIGHT_ADD_DISTRIB, MULT_CLAUSES]) >> strip_tac >> decide_tac) >>
  `w2n (addr + 32w + n2w index * n2w stride) = w2n addr + 32 + index * stride` by
    (irule abi_static_loop_child_address >> first_assum MATCH_ACCEPT_TAC) >>
  rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed native runtime array index bounds: " ^ name)
  end) (DB.thms "abiNativeArrayBounds")
