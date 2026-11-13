Theory extRetEncoderInterfacePtr
Ancestors
  extRetFramedChildPtr extRetRecursiveResourcePtr extRetSemanticResultPtr
  extRetSemanticComplexOuterPtr extRetSemanticDynamicConstructorPtr
  extRetSemanticLedgerProbePtr appendStorageGhostPtr
  bodyPtrDefs compileEnv loweringStateRelDefs ptrDiscipline venomState
  finite_map words list arithmetic pred_set

(* Resource restriction and ancestor-cell protection are already provided by
   encoder_resource_restrict and encoder_resource_push.  In particular the
   source interval q,len remains the ROOT interval when entering a child;
   replacing it by the child's interval would lose protection of siblings.
   Destination allocation and all live ancestor cells belong in protected. *)

Theorem encoder_framed_child_result_covers:
  encoder_framed_child_result D ctx fn PG sa sb sites q source_len protected
    b cap out n cost G tn s Gf tnf sf /\
  not_fresh_at sa dst /\ ptr_covers G tn dst s extent ==>
  ptr_covers Gf tnf dst sf extent
Proof
  strip_tac >> irule ptr_covers_old_transport >>
  qexists `sa` >> fs[encoder_framed_child_result_def]
QED

(* An arbitrary live child entry, with two ancestor cells (for example the
   parent array's index and tail cursor).  No source/destination provenance
   is required by the empty encoder; existing destination coverage survives.
   Neither sp nor its ghost is identified with the root entry state. *)
Theorem encoder_empty_child_with_ancestors:
  compile_abi_encode_to_buf dst src (AbiComplex []) sa = (out,sb) /\
  sp.vs_current_bb = sa.cs_current_bb /\
  sp.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~sp.vs_halted /\
  encoder_resource ctx fn sites q source_len protected sp /\
  children SUBSET sites /\ pid NOTIN children /\ cid NOTIN children /\
  FLOOKUP sp.vs_allocas pid = SOME (p,32) /\
  FLOOKUP sp.vs_allocas cid = SOME (c,32) /\
  vyper_to_abi env ty v = SOME av /\
  LENGTH (enc (vyper_to_abi_type env ty) av) = 0 ==>
  encoder_semantic_framed_result env ty v D ctx fn PG sa sb
    children q source_len ((pid,p,32)::(cid,c,32)::protected)
    b cap out 0 0 Gp tnp sp Gp tnp sp
Proof
  strip_tac >> irule encoder_semantic_complex_empty_counted_ptr >>
  qexists `av` >> simp[] >>
  irule encoder_resource_push >> qexists `children` >> simp[] >>
  irule encoder_resource_push >> qexists `sites` >> simp[]
QED
