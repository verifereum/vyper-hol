Theory placeStorageNormalizationFrame
Ancestors
  exprSimCopy typedMemoryCopy placeMemoryCopyEffect

(* Typed normalization changes only its allocated buffer.  The source
   semantic state, including all locals and immutables, is unchanged. *)
Theorem typed_copy_buffer_state_rel:
  !ctx func cenv cx es sa sb s t inst b sz.
    stmt_state_rel ctx func cenv cx es s /\
    local_ptrs_reserved cenv sa /\
    typed_copy_effect ctx func sa sb s t b sz /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
    (!name lb len. local_region cenv es.scopes s name lb len ==>
       b + sz <= lb \/ lb + len <= b) ==>
    stmt_state_rel ctx func cenv cx es t
Proof
  rpt strip_tac >>
  irule copy_buffer_state_rel_frame >>
  qexistsl_tac [`b`, `inst`, `s`, `sa`, `sz`] >>
  simp[] >>
  drule typed_copy_effect_record >> strip_tac >>
  drule typed_return_copy_static >> strip_tac >>
  fs[typed_copy_effect_def] >>
  metis_tac[arithmeticTheory.ADD_COMM]
QED
