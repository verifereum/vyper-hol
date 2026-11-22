(* Slot relations shared by supplied arguments and omitted defaults. *)
structure groupedRejectSlotsLib =
struct
open HolKernel boolLib bossLib
open compileEnvTheory abiDecoderCoherenceTheory loweringStateRelDefsTheory
     bodyPtrDefsTheory valueEncodingDefsTheory venomStateTheory venomInstTheory
     vyperTypingTheory vyperABITheory finite_mapTheory wordsTheory

val row22_kw_abi = ``\ce env (name:string,op:operand,ty:type,e:expr) tv.
  abi_decoder_coherent ce env ce.ce_struct_fields ty tv``;

val row22_kw_alloc = ``\sa s G tn (aid,p,base,tv).
  aid < sa.cs_next_id /\ not_fresh_at sa p /\ base < dimword (:256) /\
  FLOOKUP s.vs_allocas aid = SOME (base,type_memory_size tv) /\
  lookup_var p s = SOME (n2w base) /\ ptr_covers G tn p s (type_memory_size tv)``;

val row22_kw_initialized = ``\sa s G tn (aid,p,base,tv,v).
  ^row22_kw_alloc sa s G tn (aid,p,base,tv) /\ value_has_type tv v /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==> val_in_memory tv v base mem)``;

val row22_kw_meta = ``\ce env (n:string,dst,ty,e:expr) (aid:num,p,base,tv).
  dst = Var p /\ abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
  is_abi_dynamic ce.ce_struct_fields ty = tv_abi_dynamic tv /\
  base + type_memory_size tv < dimword (:256)``;
end
