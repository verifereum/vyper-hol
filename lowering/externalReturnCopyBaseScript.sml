(* Compiler-facing base equations for return normalization. *)
Theory externalReturnCopyBase
Ancestors
  externalReturnCopyBoundary context compileEnv fragExec valueEncoding

Theorem return_typed_copy_bytes_dispatch:
  ~is_word_type dty /\ is_bytestring_type dty /\ is_bytestring_type sty ==>
  compile_store_memory_typed cenv dst dty src sty =
    compile_store_bytestring src dst
Proof
  simp[Once compile_store_memory_typed_def]
QED

Theorem return_typed_copy_empty_tuple:
  acyclic_struct_metadata cenv.ce_struct_fields ==>
  compile_store_memory_typed cenv dst (TupleT []) src (TupleT []) =
    comp_return ()
Proof
  simp[Once compile_store_memory_typed_def, is_word_type_def,
       is_bytestring_type_def, compile_store_memory_typed_def]
QED

Theorem return_typed_copy_empty_struct:
  acyclic_struct_metadata cenv.ce_struct_fields /\
  get_struct_fields cenv.ce_struct_fields (nsid_to_string dn) = [] /\
  get_struct_fields cenv.ce_struct_fields (nsid_to_string sn) = [] ==>
  compile_store_memory_typed cenv dst (StructT dn) src (StructT sn) =
    comp_return ()
Proof
  simp[Once compile_store_memory_typed_def, is_word_type_def,
       is_bytestring_type_def, compile_store_memory_typed_def]
QED

Theorem return_typed_bytestring_copy_extent_explicit:
  compile_store_memory_typed cenv dst dty src sty sa = ((),sb) /\
  ~is_word_type dty /\ is_bytestring_type dty /\ is_bytestring_type sty /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  (!x. dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s0 = SOME a /\ eval_operand dst s0 = SOME d /\
  mem_word_at (w2n a) s0.vs_memory = n2w L /\
  32 + 32 * word_size L < dimword (:256) /\
  val_in_memory tv v (w2n a) s0.vs_memory /\ val_wf tv v /\
  val_footprint tv v <= 32 + 32 * word_size L /\
  32 + 32 * word_size L <= D ==>
  frag_exec ctx sa sb (\s. s = s0)
    (\t. val_in_memory tv v (w2n d) t.vs_memory /\
         (t with <|vs_vars := s0.vs_vars; vs_memory := s0.vs_memory;
                   vs_prev_bb := s0.vs_prev_bb;
                   vs_current_bb := s0.vs_current_bb;
                   vs_inst_idx := s0.vs_inst_idx|>) = s0 /\
         (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s0) /\
         (!p n. p + n <= w2n d \/ w2n d + D <= p ==>
           mem_bytes_at p n t.vs_memory = mem_bytes_at p n s0.vs_memory) /\
         LENGTH s0.vs_memory <= LENGTH t.vs_memory) (\r. F)
Proof
  strip_tac >> gvs[return_typed_copy_bytes_dispatch] >>
  drule return_bytestring_copy_extent_explicit >> simp[] >>
  disch_then irule >> simp[] >> qexists `L` >> simp[]
QED

Theorem return_typed_copy_empty_tuple_exec:
  acyclic_struct_metadata cenv.ce_struct_fields /\
  compile_store_memory_typed cenv dst (TupleT []) src (TupleT []) sa =
    ((),sb) ==>
  frag_exec ctx sa sb (\s. s = s0) (\t. t = s0) (\r. F)
Proof
  strip_tac >> drule return_typed_copy_empty_tuple >> strip_tac >>
  gvs[comp_return_def] >> irule frag_exec_refl >> simp[]
QED

Theorem return_typed_copy_empty_struct_exec:
  acyclic_struct_metadata cenv.ce_struct_fields /\
  get_struct_fields cenv.ce_struct_fields (nsid_to_string dn) = [] /\
  get_struct_fields cenv.ce_struct_fields (nsid_to_string sn) = [] /\
  compile_store_memory_typed cenv dst (StructT dn) src (StructT sn) sa =
    ((),sb) ==>
  frag_exec ctx sa sb (\s. s = s0) (\t. t = s0) (\r. F)
Proof
  strip_tac >>
  `compile_store_memory_typed cenv dst (StructT dn) src (StructT sn) =
     comp_return ()` by (irule return_typed_copy_empty_struct >> simp[]) >>
  gvs[comp_return_def] >> irule frag_exec_refl >> simp[]
QED

Theorem return_empty_tuple_memory_address:
  val_in_memory (TupleTV []) (ArrayV (TupleV [])) a mem ==>
  val_in_memory (TupleTV []) (ArrayV (TupleV [])) b mem
Proof
  simp[val_in_memory_def]
QED

Theorem return_empty_struct_memory_address:
  val_in_memory (StructTV []) (StructV []) a mem ==>
  val_in_memory (StructTV []) (StructV []) b mem
Proof
  simp[val_in_memory_def]
QED
