Theory eventBytecodeEvalChecks
Ancestors planExec integer_word byte
Libs intReduce computeLib wordsLib

(* The bytestring copier uses this signed mask. Its integer conversion must
   compute fully before byte generation and the assembly safety check. *)
val () = computeLib.upd_compset intReduce.add_int_compset

Theorem event_bytestring_mask_bytes:
  encode_num_bytes_fuel 32 (w2n ((i2w (-32)) : 256 word)) =
    REPLICATE 31 (255w : word8) ++ [224w]
Proof
  EVAL_TAC
QED
