(* Physical frame observations for a successful real SHA suffix. *)
Theory bodyShaSuffixPhysicalMods
Ancestors
  allocationPathGrowth allocationGrowth stmtReasonMemory exprLoweringProps
  exprSimHash builtinHashing vyperAST vyperTypeSystem venomState finite_map

Theorem sha_suffix_physical_mods:
  expr_type e = BaseT bty /\ is_bytes_or_string_type (expr_type e) /\
  (if is_bytestring_type (expr_type e) then compile_sha256_bytes x sm
   else case expr_type e of
          BaseT (BytesT (Fixed n)) => compile_sha256_bytesm x n sm
        | _ => compile_sha256_word x sm) = (op,sb) /\
  run_inst_seq (emitted_insts sm sb) s = OK z ==>
  (!aid a k. FLOOKUP z.vs_allocas aid = SOME (a,k) ==>
    FLOOKUP s.vs_allocas aid = SOME (a,k) \/ s.vs_alloca_next <= a) /\
  s.vs_alloca_next <= z.vs_alloca_next /\
  LENGTH s.vs_memory <= LENGTH z.vs_memory /\
  z.vs_data_section = s.vs_data_section
Proof
  strip_tac >>
  drule_all_then strip_assume_tac sha256_typed_suffix_shape >>
  drule_all_then strip_assume_tac run_inst_seq_data_section >>
  drule_then assume_tac run_inst_seq_memory_length >>
  drule_then assume_tac run_inst_seq_allocation_growth >>
  drule_then assume_tac allocation_growth_next >> simp[] >>
  rpt strip_tac >> Cases_on `FLOOKUP s.vs_allocas aid` >> simp[]
  >- metis_tac[allocation_growth_new] >>
  drule_all_then assume_tac allocation_growth_old >> gvs[]
QED
