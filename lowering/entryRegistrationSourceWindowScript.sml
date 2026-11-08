(* Actual registration addresses select windows of the FULL valid calldata tuple. *)
Theory entryRegistrationSourceWindow
Ancestors
  abiValidMember abiDecoderContract abiValidMembers contractABI vyperABI
  venomState words list arithmetic

Theorem entry_registration_source_window:
  let ao = SUM (MAP abi_member_head_size pre);
      k = abi_decode_member_offset at bs ao;
      childbs = abi_decode_member_bytes at bs (DROP ao bs) in
  vyper_decode_valid_enc_tuple (pre ++ at::ats) bs bs /\
  (is_dynamic at ==> !elem. at <> Array (SOME 0) elem) /\
  mem_bytes_at 4 (LENGTH bs) (abi_decode_source CALLDATALOAD s) = bs /\
  4 + LENGTH bs < dimword (:256) /\ off = 4 + ao /\
  (dyn /\ ~prim <=> is_dynamic at) ==>
  (if dyn /\ ~prim then (n2w 4:bytes32) +
     abi_decode_load CALLDATALOAD (n2w 4 + n2w (off-4):bytes32) s
   else n2w 4 + n2w (off-4)) = n2w (4+k) /\
  vyper_decode_valid_enc at childbs /\ k + LENGTH childbs <= LENGTH bs /\
  4+k < dimword (:256) /\
  mem_bytes_at (4+k) (LENGTH childbs) (abi_decode_source CALLDATALOAD s) = childbs
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  drule_all abi_valid_member_window >>
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  simp[GSYM word_add_n2w] >>
  Cases_on `is_dynamic at` >>
  gvs[abi_decode_member_offset_def, GSYM word_add_n2w] >>
  first_assum ACCEPT_TAC
QED

Theorem entry_registration_source_window_at_ready:
  let ao = SUM (MAP abi_member_head_size pre);
      k = abi_decode_member_offset at bs ao;
      childbs = abi_decode_member_bytes at bs (DROP ao bs) in
  vyper_decode_valid_enc_tuple (pre ++ at::ats) bs bs /\
  (is_dynamic at ==> !elem. at <> Array (SOME 0) elem) /\
  mem_bytes_at 4 (LENGTH bs) (abi_decode_source CALLDATALOAD s) = bs /\
  4 + LENGTH bs < dimword (:256) /\ off = 4 + ao /\
  (dyn /\ ~prim <=> is_dynamic at) /\ ready.vs_call_ctx = s.vs_call_ctx ==>
  (if dyn /\ ~prim then (n2w 4:bytes32) +
     abi_decode_load CALLDATALOAD (n2w 4 + n2w (off-4):bytes32) ready
   else n2w 4 + n2w (off-4)) = n2w (4+k) /\
  vyper_decode_valid_enc at childbs /\ k + LENGTH childbs <= LENGTH bs /\
  4+k < dimword (:256) /\
  mem_bytes_at (4+k) (LENGTH childbs) (abi_decode_source CALLDATALOAD ready) = childbs
Proof
  simp_tac bool_ss [LET_THM] >> strip_tac >>
  `abi_decode_source CALLDATALOAD ready = abi_decode_source CALLDATALOAD s` by
    simp[abi_decode_source_def] >>
  drule_all (SIMP_RULE bool_ss [LET_THM] entry_registration_source_window) >>
  simp[abi_decode_source_def, abi_decode_load_def]
QED

val () =
  List.app (fn th =>
    let val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
    in if null axioms andalso null (Thm.hyp th) andalso
          List.all (fn name => name = "DISK_THM") oracles
       then ()
       else raise Fail "registration source window inherited admission"
    end)
    [entry_registration_source_window, entry_registration_source_window_at_ready];
val () = print "ENTRY_REGISTRATION_SOURCE_WINDOW_AUDIT OK\n";
