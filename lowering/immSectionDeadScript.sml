(* The constructor's immutables fixed region and the bytes an immutables
 * section leaves dead, shared by the deployment composition
 * (ctorDeployDefs) and the pointer body judgments (bodyPtrDefs), whose
 * constructor instance lets taint sit only on those bytes.
 * TOP-LEVEL: imm_len, mem_dead_bytes, imm_section_dead.
 *)
Theory immSectionDead
Ancestors
  compileVyper compileEnv valueEncoding vyperValue vyperContext vyperAST
  words list

(* Bytes of the constructor's immutables fixed region, at memory offset 0. *)
Definition imm_len_def:
  imm_len tops =
    compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) tops
End

(* mem_dead_bytes sec off tv i: byte i of sec is dead in a value of type tv
   laid out from byte off of sec in memory layout, by the lengths sec itself
   holds (the memory twin of dead_bytes):
   - a bytestring: a data byte at or past the length, within the capacity;
   - a DynArray: every byte of an element at or past the length, and the
     dead bytes of the elements below it;
   - a struct, tuple or static array: the dead bytes of its members.
   These are the bytes immutable_value_mask leaves unused. *)
Definition mem_dead_bytes_def:
  (mem_dead_bytes (sec:word8 list) off (BaseTV (BytesT (Dynamic max))) i <=>
     off + 32 + w2n (mem_word_at off sec) <= i /\
     i < off + type_memory_size (BaseTV (BytesT (Dynamic max)))) /\
  (mem_dead_bytes sec off (BaseTV (StringT max)) i <=>
     off + 32 + w2n (mem_word_at off sec) <= i /\
     i < off + type_memory_size (BaseTV (StringT max))) /\
  (mem_dead_bytes sec off (BaseTV _) i <=> F) /\
  (mem_dead_bytes sec off (FlagTV _) i <=> F) /\
  (mem_dead_bytes sec off NoneTV i <=> F) /\
  (mem_dead_bytes sec off (TupleTV tvs) i <=>
     mem_dead_bytes_list sec off tvs i) /\
  (mem_dead_bytes sec off (ArrayTV tv (Fixed n)) i <=>
     ?k. k < n /\ mem_dead_bytes sec (off + k * type_memory_size tv) tv i) /\
  (mem_dead_bytes sec off (ArrayTV tv (Dynamic n)) i <=>
     ?k. k < n /\
         if k < w2n (mem_word_at off sec) then
           mem_dead_bytes sec (off + 32 + k * type_memory_size tv) tv i
         else
           off + 32 + k * type_memory_size tv <= i /\
           i < off + 32 + (k + 1) * type_memory_size tv) /\
  (mem_dead_bytes sec off (StructTV fields) i <=>
     mem_dead_bytes_fields sec off fields i) /\
  (mem_dead_bytes_list sec off [] i <=> F) /\
  (mem_dead_bytes_list sec off (tv::tvs) i <=>
     mem_dead_bytes sec off tv i \/
     mem_dead_bytes_list sec (off + type_memory_size tv) tvs i) /\
  (mem_dead_bytes_fields sec off [] i <=> F) /\
  (mem_dead_bytes_fields sec off ((_,tv)::fields) i <=>
     mem_dead_bytes sec off tv i \/
     mem_dead_bytes_fields sec (off + type_memory_size tv) fields i)
End

(* Byte j of an immutables section sec is dead in some immutable's value. *)
Definition imm_section_dead_def:
  imm_section_dead tops sec j <=>
    ?pre vis name ty slot post tv.
      tops = pre ++ VariableDecl vis Immutable name ty slot :: post /\
      evaluate_type (type_env tops) ty = SOME tv /\
      mem_dead_bytes sec
        (compute_immutables_len (get_struct_fields (make_struct_fields_map tops)) pre)
        tv j
End
