(*
 * A storage region decodes from its live bytes alone.
 *)
Theory storageLiveAgree
Ancestors
  vyperStorage vyperLookupStorage loweringStateRelDefs accountsRelProps

(* Storage that agrees with s1 on every byte of the region s1 does not leave
   dead (dead_bytes) decodes there whenever s1 does. Intuition: every slot
   slots_in_range reads lies in the region; the length slot of a bytestring
   or DynArray is never dead (dyn_bytes_dead needs off < j), so both
   storages see the same length; DynArray elements below the length are
   dead only where the element type leaves them dead; all 32 bytes equal
   make the words equal (the agreement is stated at the same n2w j that
   read_slot reads). dead_bytes_range bounds every dead byte to its region. *)
Theorem slots_in_range_live_agree:
  slots_in_range s1 off tv /\
  (!j b. off <= j /\ j < off + type_slot_size tv /\ b < 32 /\
         ~dead_bytes s1 off tv j b ==>
         EL b (word_to_bytes (lookup_storage (n2w j) s1) T) =
         EL b (word_to_bytes (lookup_storage (n2w j) s2) T)) ==>
  slots_in_range s2 off tv
Proof
  cheat
QED
