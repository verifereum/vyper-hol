(* Concrete owner transport for exact primitive-word registration. *)
Theory defaultConcreteWordRegistration
Ancestors defaultConcreteRegistrationDefs defaultConcreteRegistrationInit
  defaultWordRegistration abiDecoderContract valueEncodingProps
  decoderGhostFramePtr bodyPtrDefs abiDecoderReentry freshWrites
  compileEnv finite_map words

Theorem default_registration_owner_frame:
  default_registration_owner fn ce st s G tn ((name,ty),tv) (x,dst,p,id) /\
  FLOOKUP ce'.ce_vars name = FLOOKUP ce.ce_vars name /\
  st.cs_next_id <= st'.cs_next_id /\
  (!v. not_fresh_at st v ==> not_fresh_at st' v /\
    FLOOKUP H v = FLOOKUP G v /\
    op_taint u (Var v) = op_taint tn (Var v) /\
    eval_operand (Var v) t = eval_operand (Var v) s) /\
  FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id /\
  s.vs_alloca_next <= t.vs_alloca_next /\
  abi_decode_frame s.vs_alloca_next n s t ==>
  default_registration_owner fn ce' st' t H u ((name,ty),tv) (x,dst,p,id)
Proof
  simp[default_registration_owner_def] >> strip_tac >>
  `val_in_memory tv x p t.vs_memory` by
    (irule val_in_memory_mem_agree >> simp[] >>
     qexistsl [`type_memory_size tv`, `s.vs_memory`] >>
     gvs[abi_decode_frame_def] >> metis_tac[]) >>
  `ptr_covers H u vname t (type_memory_size tv)` by
    (irule ptr_covers_frame >> qexistsl [`G`,`s`,`tn`] >>
     fs[venomStateTheory.eval_operand_def]) >>
  rpt (goal_assum $ drule_at Any) >> simp[] >> gvs[] >> metis_tac[]
QED
