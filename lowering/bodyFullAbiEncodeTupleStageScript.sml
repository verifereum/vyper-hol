(* Conditional fold of actual compiler slots. P carries the complete caller
   invariant; the concrete slot producer and its resource frames discharge
   the step at the caller join. This is not a concrete execution theorem. *)
Theory bodyFullAbiEncodeTupleStage
Ancestors
  abiTupleProps exprLowering compileEnv context list pair arithmetic

Theorem abi_encode_tuple_compiler_step[local]:
  compile_store_abi_tuple ce buf off ((op,ty)::xs) a =
  (do compile_abi_tuple_slot ce buf off op ty;
      compile_store_abi_tuple ce buf (off+type_memory_bytes ce ty) xs od) a
Proof
  simp[compile_store_abi_tuple_def, compile_abi_tuple_slot_def,
       comp_bind_def, comp_ignore_bind_def] >>
  Cases_on `emit_op ADD [buf; Lit (n2w off)] a` >> simp[]
QED

Theorem abi_encode_owned_tuple_stage:
  (!a r. E a r a r) /\
  (!a r b s c t. E a r b s /\ E b s c t ==> E a r c t) /\
  (!done rest off a b r op ty.
    compile_abi_tuple_slot ce buf off op ty a = ((),b) /\
    P done ((op,ty)::rest) off a r ==>
    ?s. E a r b s /\
      P (done ++ [(op,ty)]) rest
        (off + type_memory_bytes ce ty) b s) ==>
  !xs done off a b r.
    compile_store_abi_tuple ce buf off xs a = ((),b) /\
    P done xs off a r ==>
    ?s. E a r b s /\
      P (done ++ xs) [] (off + abi_tuple_bytes ce xs) b s
Proof
  strip_tac >> Induct
  >- (simp[compile_store_abi_tuple_def, comp_return_def, abi_tuple_bytes_def] >>
      metis_tac[]) >>
  gen_tac >> PairCases_on `h` >> rpt gen_tac >>
  rewrite_tac[abi_encode_tuple_compiler_step, comp_ignore_bind_def, comp_bind_def] >>
  Cases_on `compile_abi_tuple_slot ce buf off h0 h1 a` >>
  rename1 `compile_abi_tuple_slot ce buf off h0 h1 a = (u,mid)` >>
  Cases_on `u` >> simp[] >> strip_tac >>
  qpat_x_assum `!done rest off a b r op ty. _` drule_all >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  qexists_tac `s''` >> conj_tac >- metis_tac[] >>
  qpat_x_assum `P (_ ++ _ ++ _) [] _ _ _` mp_tac >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >>
  simp_tac (srw_ss()) [ADD_ASSOC, abi_tuple_bytes_def]
QED
