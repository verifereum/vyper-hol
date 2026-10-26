(* Execute a recursive array child at an arbitrary cursor and retain the prefix. *)
Theory abiDecoderRecursiveArrayIteration
Ancestors
  abiDecoderArrayBody abiDecoderRecursiveLoopInvariant abiDecoderArrayInvariant
  abiDecoderArraySlice abiDecoderCoherence abiDecoderTypedContract abiDecoderEffect
  abiDecoderProtectedScratch abiDecoderAllocation abiDecoderContract
  abiDecoderCorrect abiDecoderLoop abiDecoderReentry compileEnv valueEncoding
  vyperABI vyperValue venomState words list rich_list arithmetic

Theorem abi_decoder_effect_ranges:
  abi_decoder_effect first last lo hi next limit_st out outsz b cap s t /\
  abi_decoder_operand_live next src /\ abi_decoder_operand_live next dst /\
  abi_decoder_operand_live next hi_op /\
  abi_decoder_ranges opc hi_op src dst sb len d sz b cap s ==>
  abi_decoder_ranges opc hi_op src dst sb len d sz b cap t
Proof
  rw[abi_decoder_ranges_def, abi_decoder_effect_def] >> metis_tac[]
QED

Theorem abi_decoder_array_body_at_index:
  abi_decode_array_element_setup ip src dst opc hi (type_to_abi_dec_info sf ce ty)
    (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty) st = (ops,middle) /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) opc hi
    (type_to_abi_dec_info sf ce ty) middle = ((),end_st) /\
  fn_has_code st end_st func /\
  (!bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  abi_decoder_correct ce env sf ty tv /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    parent_di (ListV avs) (ArrayV (DynArrayV vs)) /\
  abi_decoder_array_memory opc (vyper_to_abi_type env ty) avs tv vs sb d j initial /\
  j < LENGTH vs /\
  abi_decoder_ranges opc hi src dst sb
    (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial /\
  eval_operand ip initial = SOME p /\ mload (w2n p) initial = n2w j /\
  abi_decoder_operand_live st.cs_next_var src /\ abi_decoder_operand_live st.cs_next_var dst /\
  abi_decoder_operand_live st.cs_next_var hi /\ abi_decoder_operand_live st.cs_next_var ip /\
  abi_decoder_budget first last b cap initial /\ first <= st.cs_next_id /\
  st.cs_next_id <= middle.cs_next_id /\ end_st.cs_next_id <= last /\
  end_st.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st initial /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?actual. val_in_memory tv (EL j vs) (d + 32 + j * type_memory_bytes ce ty) actual.vs_memory /\
    abi_decoder_effect first last st.cs_next_id end_st.cs_next_id st.cs_next_var limit_st
      (d + 32 + j * type_memory_bytes ce ty) (type_memory_bytes ce ty) b cap initial actual /\
    eval_operand (FST ops) actual = SOME (n2w j) /\ eval_operand ip actual = SOME p /\
    actual.vs_current_bb = end_st.cs_current_bb /\
    actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\ ~actual.vs_halted /\
    abi_decode_sim ctx func initial actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule abi_decoder_dynarray_values >> strip_tac >>
  `j < LENGTH avs` by decide_tac >>
  `TAKE j avs ++ EL j avs::DROP (SUC j) avs = avs` by
    (mp_tac (Q.ISPEC `avs:abi_value list` (Q.SPEC `j:num` TAKE_DROP_SUC)) >>
     asm_simp_tac bool_ss [GSYM APPEND_ASSOC, APPEND]) >>
  `TAKE j vs ++ EL j vs::DROP (SUC j) vs = vs` by
    (mp_tac (Q.ISPEC `vs:vyperValue$value list` (Q.SPEC `j:num` TAKE_DROP_SUC)) >>
     asm_simp_tac bool_ss [GSYM APPEND_ASSOC, APPEND]) >>
  `LENGTH (TAKE j avs) = j /\ LENGTH (TAKE j vs) = j` by simp[LENGTH_TAKE, MIN_DEF] >>
  qpat_assum `abi_decoder_array_memory _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_array_memory_def]) >>
  mp_tac (Q.INST [`pre` |-> `TAKE j (avs:abi_value list)`, `av` |-> `EL j (avs:abi_value list)`,
    `post` |-> `DROP (SUC j) (avs:abi_value list)`, `vpre` |-> `TAKE j (vs:vyperValue$value list)`,
    `v` |-> `EL j (vs:vyperValue$value list)`, `vpost` |-> `DROP (SUC j) (vs:vyperValue$value list)`]
    abi_decoder_array_body) >>
  asm_simp_tac bool_ss []
QED

Theorem abi_decoder_recursive_body_inputs:
  abi_decoder_recursive_loop_inv opc aty avs tv vs sb d outsz slot site
    first last lo hi next limit_st b cap initial body_lbl j s /\
  abi_decoder_ranges opc hi_op src dst sb (LENGTH (enc (Array NONE aty) (ListV avs)))
    d outsz b cap initial /\
  abi_decoder_operand_live next src /\ abi_decoder_operand_live next dst /\
  abi_decoder_operand_live next hi_op /\ abi_decoder_operand_live next ip /\
  eval_operand ip initial = SOME (n2w slot) /\ slot < dimword (:256) /\ next <= body_next ==>
  abi_decoder_array_memory opc aty avs tv vs sb d j s /\
  abi_decoder_ranges opc hi_op src dst sb (LENGTH (enc (Array NONE aty) (ListV avs)))
    d outsz b cap s /\
  fresh_vars_wrt limit_st s /\ abi_decoder_budget first last b cap s /\
  eval_operand ip s = SOME (n2w slot) /\ mload (w2n (n2w slot:bytes32)) s = n2w j /\
  abi_decoder_operand_live body_next src /\ abi_decoder_operand_live body_next dst /\
  abi_decoder_operand_live body_next hi_op /\ abi_decoder_operand_live body_next ip /\
  s.vs_current_bb = body_lbl /\ s.vs_inst_idx = 0 /\ ~s.vs_halted
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `abi_decoder_recursive_loop_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_recursive_loop_inv_def]) >>
  drule_all abi_decoder_effect_ranges >> strip_tac >>
  `fresh_vars_wrt limit_st s /\ abi_decoder_budget first last b cap s /\
    eval_operand ip s = SOME (n2w slot)` by
    (fs[abi_decoder_effect_def, Excl "enc_def"] >> metis_tac[]) >>
  asm_simp_tac bool_ss [w2n_n2w, LESS_MOD] >>
  metis_tac[abi_decoder_operand_live_mono]
QED

(* TOP-LEVEL: the generated body extends the initialized prefix even when its
   recursive child allocates scratch and changes the current basic block. *)
Theorem abi_decoder_recursive_array_iteration:
  abi_decode_array_element_setup ip src dst opc hi_op (type_to_abi_dec_info sf ce ty)
    (abi_embedded_static_size ce.ce_struct_fields ty) (type_memory_bytes ce ty) st = (ops,middle) /\
  compile_abi_decode_to_buf (SND (SND ops)) (FST (SND ops)) opc hi_op
    (type_to_abi_dec_info sf ce ty) middle = ((),end_st) /\
  fn_has_code st end_st func /\ st.cs_current_insts = [] /\
  (!bb. lookup_block end_st.cs_current_bb func.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0) /\
  abi_decoder_correct ce env sf ty tv /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  abi_decoder_metadata ce env (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn))
    parent_di (ListV avs) (ArrayV (DynArrayV vs)) /\
  abi_decoder_recursive_loop_inv opc (vyper_to_abi_type env ty) avs tv vs sb d
    (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) slot site
    first last lo hi next limit_st b cap initial st.cs_current_bb j s /\ j < LENGTH vs /\
  abi_decoder_ranges opc hi_op src dst sb
    (LENGTH (enc (Array NONE (vyper_to_abi_type env ty)) (ListV avs)))
    d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial /\
  abi_decoder_operand_live next src /\ abi_decoder_operand_live next dst /\
  abi_decoder_operand_live next hi_op /\ abi_decoder_operand_live next ip /\
  eval_operand ip initial = SOME (n2w slot) /\ slot < dimword (:256) /\
  first <= lo /\ lo <= st.cs_next_id /\ st.cs_next_id <= middle.cs_next_id /\
  end_st.cs_next_id <= hi /\ hi <= last /\ next <= st.cs_next_var /\
  first <= site /\ site < last /\ (site < st.cs_next_id \/ end_st.cs_next_id <= site) /\
  end_st.cs_next_var <= limit_st.cs_next_var ==>
  ?actual. abi_decoder_array_memory opc (vyper_to_abi_type env ty) avs tv vs sb d (SUC j) actual /\
    abi_decoder_effect first last lo hi next limit_st
      d (type_memory_bytes ce (ArrayT ty (Dynamic maxn))) b cap initial actual /\
    FLOOKUP actual.vs_allocas site = SOME (slot,32) /\ mload slot actual = n2w j /\
    eval_operand (FST ops) actual = SOME (n2w j) /\
    eval_operand ip actual = SOME (n2w slot) /\
    actual.vs_current_bb = end_st.cs_current_bb /\
    actual.vs_inst_idx = LENGTH end_st.cs_current_insts /\ ~actual.vs_halted /\
    abi_decode_sim ctx func s actual
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`body_next` |-> `st.cs_next_var`, `body_lbl` |-> `st.cs_current_bb`,
    `aty` |-> `vyper_to_abi_type env ty`,
    `outsz` |-> `type_memory_bytes ce (ArrayT ty (Dynamic maxn))`]
    abi_decoder_recursive_body_inputs) >>
  impl_tac >- asm_simp_tac bool_ss [] >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `first <= st.cs_next_id /\ end_st.cs_next_id <= last` by decide_tac >>
  `s.vs_inst_idx = LENGTH st.cs_current_insts` by simp[] >>
  drule_all (Q.INST [`initial` |-> `s:venom_state`, `p` |-> `n2w slot:bytes32`]
    abi_decoder_array_body_at_index) >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule abi_decoder_dynarray_values >> strip_tac >>
  `abi_decoder_coherent ce env sf ty tv` by fs[abi_decoder_coherent_array_iff] >>
  `type_memory_size tv = type_memory_bytes ce ty` by
    metis_tac[abi_decoder_coherent_header, abi_decoder_header_def] >>
  `j < maxn` by decide_tac >>
  `j * type_memory_size tv + type_memory_size tv <= maxn * type_memory_size tv`
    by simp[abi_decoder_array_cell_capacity] >>
  `d + 32 + j * type_memory_bytes ce ty + type_memory_bytes ce ty <=
    d + type_memory_bytes ce (ArrayT ty (Dynamic maxn))`
    by (qpat_x_assum `j * type_memory_size tv + type_memory_size tv <= _` mp_tac >>
        simp_tac bool_ss [Once type_memory_bytes_def] >>
        asm_simp_tac bool_ss [] >> decide_tac) >>
  qpat_assum `abi_decoder_ranges _ _ _ _ _ _ _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_decoder_ranges_def]) >>
  qpat_assum `type_memory_size tv = _`
    (fn size => mp_tac (PURE_REWRITE_RULE [size]
      (Q.INST [`child_lo` |-> `st.cs_next_id`, `child_hi` |-> `end_st.cs_next_id`,
        `child_next` |-> `st.cs_next_var`, `body_lbl` |-> `st.cs_current_bb`,
        `aty` |-> `vyper_to_abi_type env ty`, `t` |-> `actual:venom_state`,
        `outsz` |-> `type_memory_bytes ce (ArrayT ty (Dynamic maxn))`]
        abi_decoder_recursive_child_advance))) >>
  impl_tac >- asm_simp_tac bool_ss [] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qexists_tac `actual` >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_RECURSIVE_ARRAY_ITERATION_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI recursive array iteration not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderRecursiveArrayIteration");
