(* Canonical tuple offsets connected to the emitted member-pointer sequence. *)
Theory abiDecoderCanonicalPtr
Ancestors
  abiDecoderMemberPtr abiCanonicalLoad abiCanonicalWindows abiCanonicalArrayLoad
  abiDecodeRanges abiDecoderContract contractABI valueEncoding
  venomExecSemantics venomState words arithmetic list

Theorem canonical_tuple_dynamic_child_source:
  has_types (pre ++ ty::post) (pvs ++ v::rest) /\
  LENGTH pre = LENGTH pvs /\ is_dynamic ty /\
  mem_bytes_at sb (LENGTH (enc (Tuple (pre ++ ty::post))
    (ListV (pvs ++ v::rest)))) source =
      enc (Tuple (pre ++ ty::post)) (ListV (pvs ++ v::rest)) ==>
  mem_bytes_at (sb + head_lengths (pre ++ ty::post) 0 +
                SUM (MAP2 abi_member_tail_size pre pvs)) (LENGTH (enc ty v)) source =
    enc ty v
Proof
  strip_tac >> drule_all canonical_member_ranges >>
  asm_simp_tac bool_ss [LET_THM] >> strip_tac >>
  irule EQ_TRANS >>
  qexists_tac `TAKE (LENGTH (enc ty v))
    (DROP (head_lengths (pre ++ ty::post) 0 + SUM (MAP2 abi_member_tail_size pre pvs))
      (enc (Tuple (pre ++ ty::post)) (ListV (pvs ++ v::rest))))` >>
  conj_tac
  >- (pure_rewrite_tac[GSYM ADD_ASSOC] >>
      qpat_assum `mem_bytes_at sb _ source = _` (fn th =>
        CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [GSYM th]))) >>
      irule EQ_SYM >> irule mem_bytes_at_window >>
      asm_simp_tac arith_ss [head_lengths_acc]) >>
  irule canonical_member_tail_window >> simp[]
QED

Theorem abi_decode_canonical_dynamic_member_pointer_sentinel:
  compile_getelemptr_abi src T (SUM (MAP abi_member_head_size pre)) opc (Lit 0w)
    st = (member_op,st') /\
  has_types (pre ++ ty::post) (pvs ++ v::rest) /\
  LENGTH pre = LENGTH pvs /\ is_dynamic ty /\
  abi_decode_source_opcode opc /\ eval_operand src s = SOME (n2w sb) /\
  fresh_vars_wrt st s /\
  mem_bytes_at sb (LENGTH (enc (Tuple (pre ++ ty::post))
    (ListV (pvs ++ v::rest)))) (abi_decode_source opc s) =
      enc (Tuple (pre ++ ty::post)) (ListV (pvs ++ v::rest)) /\
  sb + LENGTH (enc (Tuple (pre ++ ty::post)) (ListV (pvs ++ v::rest))) <
    dimword (:256) ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand member_op t = SOME (n2w (sb + head_lengths (pre ++ ty::post) 0 +
      SUM (MAP2 abi_member_tail_size pre pvs))) /\
    mem_bytes_at (sb + head_lengths (pre ++ ty::post) 0 +
      SUM (MAP2 abi_member_tail_size pre pvs)) (LENGTH (enc ty v))
      (abi_decode_source opc t) = enc ty v /\
    fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ inst_extends st st'
Proof
  strip_tac >> drule_all canonical_member_offset_load >> strip_tac >>
  drule_all abi_decode_dynamic_member_pointer_sentinel >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st st') s = OK t` >>
  `mem_bytes_at (sb + head_lengths (pre ++ ty::post) 0 +
     SUM (MAP2 abi_member_tail_size pre pvs)) (LENGTH (enc ty v))
     (abi_decode_source opc s) = enc ty v` by
    (irule canonical_tuple_dynamic_child_source >> asm_simp_tac bool_ss [] >>
     qexists_tac `rest` >> asm_simp_tac bool_ss []) >>
  qexists_tac `t` >> gvs[abi_decode_source_def] >> simp[ADD_ASSOC]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_CANONICAL_PTR_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI canonical member pointer not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderCanonicalPtr");
