structure compilerParityCompsetLib = struct

(* Configure the caller's computation set after its ancestors have loaded. *)
fun prepare {byte_updates} =
  (computeLib.upd_compset finite_mapLib.add_finite_map_compset;
   computeLib.upd_compset (computeLib.add_thms
     ([alistTheory.fmap_to_alist_FEMPTY, integer_wordTheory.i2w_pos] @
      (if byte_updates then [byteTheory.set_byte_bit_field_insert] else []))));

end
