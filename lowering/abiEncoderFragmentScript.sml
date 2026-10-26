(* Source-value fragment API for the recursive descriptor/window encoder.
   The statement preserves the to_buf clause consumed by external returns.
   The legacy mutual theorem has an obsolete dyn_loop clause; this theorem
   does not use that admitted theorem or change its statement. *)
Theory abiEncoderFragment
Ancestors
  abiEncoderProps abiScratchEncoderRecursive abiScratchEncoderContract
  abiEncoderCorrectRecursive abiEncoderInput abiEncoderAdmissible
  fragExec compileEnv valueEncoding vyperABI vyperTyping contractABI
  venomState venomExecSemantics words list

(* enc_pre allows stale fresh variables: the bridge must preserve that
   generality. Its scratch bounds already imply source/output nonwrapping.
   abi_enc_plan is a semantic descriptor relation, so exact syntactic type
   translation is not an additional premise. *)
Theorem compile_abi_encode_to_buf_frag:
  !dst src ei st op st' ctx env ty tv v av s0 dst_w src_w lo top.
    compile_abi_encode_to_buf dst src ei st = (op, st') /\
    abi_enc_plan env ty ei /\
    evaluate_type env ty = SOME tv /\ value_has_type tv v /\
    vyper_to_abi env ty v = SOME av /\
    eval_operand dst s0 = SOME dst_w /\ eval_operand src s0 = SOME src_w /\
    enc_pre st st' [dst; src] lo top tv v (w2n src_w)
      [(w2n dst_w, LENGTH (enc (vyper_to_abi_type env ty) av))] s0 ==>
    frag_exec ctx st st' (\s. s = s0)
      (\s. mem_bytes_at (w2n dst_w)
             (LENGTH (enc (vyper_to_abi_type env ty) av)) s.vs_memory =
           enc (vyper_to_abi_type env ty) av /\
           eval_operand op s =
             SOME (n2w (LENGTH (enc (vyper_to_abi_type env ty) av))) /\
           enc_frame st st' lo top
             [(w2n dst_w, LENGTH (enc (vyper_to_abi_type env ty) av))] s0 s)
      (\r. F)
Proof
  (* Temporary admission while the independent statement check and Alan
     bridge task establish the source representation and exact frame. *)
  cheat
QED
