(* TOP-LEVEL: existing topic operands survive an encoder, and the concrete
   aggregate arena bounds make its emitted LOG byte count exact. *)
Theory abiLogReady
Ancestors
  abiFlatFieldsDefs abiFieldLayoutDefs abiFieldTypedSource abiFieldOperands
  contractABI venomState list words arithmetic

Theorem eval_operands_pointwise_frame:
  !ops before after.
    (!arg_op. eval_operand arg_op after = eval_operand arg_op before) ==>
    eval_operands ops after = eval_operands ops before
Proof
  Induct_on `ops` >- simp[eval_operands_def] >> rpt gen_tac >> DISCH_TAC >>
  qpat_x_assum `!before after. _` (qspecl_then [`before`, `after`] mp_tac) >>
  simp[eval_operands_def]
QED

Theorem eval_operands_before_frame:
  !ops bound before after.
    EVERY (abi_operand_before bound) ops /\
    (!arg_op. abi_operand_before bound arg_op ==>
      eval_operand arg_op after = eval_operand arg_op before) ==>
    eval_operands ops after = eval_operands ops before
Proof
  Induct_on `ops` >> simp[eval_operands_def] >> rpt strip_tac >> fs[] >>
  qpat_x_assum `!bound before after. _`
    (qspecl_then [`bound`, `before`, `after`] mp_tac) >> simp[]
QED

Theorem abi_flat_source_encoded_length:
  !rows tys avs dst dyn capacity.
    has_types tys avs /\
    MAP abi_flat_output rows = MAP2 (\ty v. (is_dynamic ty,enc ty v)) tys avs /\
    abi_flat_geometry [] rows (abi_field_head_size (MAP abi_flat_output rows)) dst dyn capacity ==>
    LENGTH (enc (Tuple tys) (ListV avs)) < dimword(:256)
Proof
  rpt gen_tac >> strip_tac >> drule_all enc_typed_tuple_field_bytes >> DISCH_TAC >>
  `LENGTH (enc (Tuple tys) (ListV avs)) =
    abi_field_head_size (MAP abi_flat_output rows) + abi_field_tail_size (MAP abi_flat_output rows)` by
    asm_simp_tac bool_ss [abi_field_bytes_length] >>
  gvs[abi_flat_geometry_def, abi_field_head_size_def, abi_field_tail_size_def] >> decide_tac
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
      List.all (fn s => s = "DISK_THM") oracles
    then () else raise Fail ("unclosed concrete Log encoder prerequisites: " ^ name)
  end) (DB.thms "abiLogReady")
