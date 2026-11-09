(* Allocation sizes at the paired decoder's actual endpoint. *)
Theory ctorDeployMemoryRunPtrPrefixEntryLiteralSizes
Ancestors
  ctorDeployMemoryRunPtrPrefixEntryDecoderShape ctorAbiActualFrame
  abiEncoderRegisteredEffect ctorAbiActualSites contextCodegenRel
  abiEncoder abiEncoderProps abiDecoderLoop exprLoweringProps fragExec finite_map words list pred_set

Theorem prefix_entry_literal_sizes_frame:
  abi_encoder_registered_effect ids outs s t /\
  (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN ids /\ FLOOKUP t.vs_allocas inst.inst_id = SOME (b,sz) ==>
    sz = 32) /\
  (!inst b sz n. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_operands = [Lit n] /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==> sz = w2n n) /\
  (!inst n. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN ids /\ inst.inst_operands = [Lit n] ==> w2n n = 32) ==>
  !inst b sz n. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_operands = [Lit n] /\
    FLOOKUP t.vs_allocas inst.inst_id = SOME (b,sz) ==> sz = w2n n
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_id IN ids`
  >- metis_tac[] >>
  fs[abi_encoder_registered_effect_def] >> metis_tac[]
QED


Theorem prefix_entry_decoder_literal_sizes:
  compile_abi_decode_to_buf dst src DLOAD hi info st = ((),last) /\
  fn_has_code st last func /\ fn_inst_ids_distinct func /\
  ctor_actual_scratch func (ctor_actual_sites func (frag_ids st last)) d cap t /\
  abi_encoder_registered_effect (ctor_actual_sites func (frag_ids st last)) outs s t /\
  (!inst b sz n. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_operands = [Lit n] /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==> sz = w2n n) ==>
  !inst b sz n. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_operands = [Lit n] /\
    FLOOKUP t.vs_allocas inst.inst_id = SOME (b,sz) ==> sz = w2n n
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_id IN ctor_actual_sites func (frag_ids st last)`
  >- (`sz = 32` by (fs[ctor_actual_scratch_def, ctor_actual_sites_def] >> metis_tac[]) >>
      `inst.inst_operands = [Lit 32w]` by
        (irule prefix_entry_decoder_alloca_shape >>
         gvs[ctor_actual_sites_def, frag_ids_def] >> metis_tac[]) >>
      gvs[wordsTheory.dimword_def, venomMemPropsTheory.dimindex_256]) >>
  fs[abi_encoder_registered_effect_def] >> metis_tac[]
QED
