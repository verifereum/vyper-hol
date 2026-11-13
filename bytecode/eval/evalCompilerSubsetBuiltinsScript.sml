(*
 * Compiler subset fixtures for supported environment and account builtins.
 *
 * The terms correspond exactly to the pinned frontend translation of the
 * sources in bytecode/python-o1-no-asm-opt-builtins-sources/.
 *)

Theory evalCompilerSubsetBuiltins
Ancestors evalCompiler

Definition env_message_core_program_def:
  env_message_core_program =
    [FunctionDecl External View F F "get_sender"
       ([] : (string # type) list) ([] : expr list) (BaseT AddressT)
       [Return (SOME (Builtin (BaseT AddressT) (Env Sender) []))];
     FunctionDecl External View F F "get_self_address"
       ([] : (string # type) list) ([] : expr list) (BaseT AddressT)
       [Return (SOME (Builtin (BaseT AddressT) (Env SelfAddr) []))];
     FunctionDecl External Payable F F "get_value_sent"
       ([] : (string # type) list) ([] : expr list) (BaseT (UintT 256))
       [Return (SOME (Builtin (BaseT (UintT 256)) (Env ValueSent) []))]]
End

Definition env_block_program_def:
  env_block_program =
    [FunctionDecl External View F F "get_timestamp"
       ([] : (string # type) list) ([] : expr list) (BaseT (UintT 256))
       [Return (SOME (Builtin (BaseT (UintT 256)) (Env TimeStamp) []))];
     FunctionDecl External View F F "get_block_number"
       ([] : (string # type) list) ([] : expr list) (BaseT (UintT 256))
       [Return (SOME (Builtin (BaseT (UintT 256)) (Env BlockNumber) []))];
     FunctionDecl External View F F "get_blob_base_fee"
       ([] : (string # type) list) ([] : expr list) (BaseT (UintT 256))
       [Return (SOME (Builtin (BaseT (UintT 256)) (Env BlobBaseFee) []))];
     FunctionDecl External View F F "get_previous_hash"
       ([] : (string # type) list) ([] : expr list) (BaseT (BytesT (Fixed 32)))
       [Return (SOME (Builtin (BaseT (BytesT (Fixed 32))) (Env PrevHash) []))];
     FunctionDecl External View F F "get_coinbase"
       ([] : (string # type) list) ([] : expr list) (BaseT AddressT)
       [Return (SOME (Builtin (BaseT AddressT) (Env Coinbase) []))];
     FunctionDecl External View F F "get_gas_limit"
       ([] : (string # type) list) ([] : expr list) (BaseT (UintT 256))
       [Return (SOME (Builtin (BaseT (UintT 256)) (Env GasLimit) []))];
     FunctionDecl External View F F "get_base_fee"
       ([] : (string # type) list) ([] : expr list) (BaseT (UintT 256))
       [Return (SOME (Builtin (BaseT (UintT 256)) (Env BaseFee) []))];
     FunctionDecl External View F F "get_difficulty"
       ([] : (string # type) list) ([] : expr list) (BaseT (UintT 256))
       [Return (SOME
          (Builtin (BaseT (UintT 256)) (Env PrevRandao) []))]]
End

Definition env_tx_chain_program_def:
  env_tx_chain_program =
    [FunctionDecl External View F F "get_gas_price"
       ([] : (string # type) list) ([] : expr list) (BaseT (UintT 256))
       [Return (SOME (Builtin (BaseT (UintT 256)) (Env GasPrice) []))];
     FunctionDecl External View F F "get_tx_origin"
       ([] : (string # type) list) ([] : expr list) (BaseT AddressT)
       [Return (SOME (Builtin (BaseT AddressT) (Env TxOrigin) []))];
     FunctionDecl External View F F "get_chain_id"
       ([] : (string # type) list) ([] : expr list) (BaseT (UintT 256))
       [Return (SOME (Builtin (BaseT (UintT 256)) (Env ChainId) []))]]
End

Definition account_items_program_def:
  account_items_program =
    [InterfaceDecl "AccountLike"
       [("ping", ([] : (string # type) list), BaseT (UintT 256), View)];
     FunctionDecl External View F F "account_address"
       [("a", BaseT AddressT)] ([] : expr list) (BaseT AddressT)
       [Return (SOME
          (Builtin (BaseT AddressT) (Acc Address)
             [Name (BaseT AddressT) "a"]))];
     FunctionDecl External View F F "account_balance"
       [("a", BaseT AddressT)] ([] : expr list) (BaseT (UintT 256))
       [Return (SOME
          (Builtin (BaseT (UintT 256)) (Acc Balance)
             [Name (BaseT AddressT) "a"]))];
     FunctionDecl External View F F "account_codehash"
       [("a", BaseT AddressT)] ([] : expr list) (BaseT (BytesT (Fixed 32)))
       [Return (SOME
          (Builtin (BaseT (BytesT (Fixed 32))) (Acc Codehash)
             [Name (BaseT AddressT) "a"]))];
     FunctionDecl External View F F "account_codesize"
       [("a", BaseT AddressT)] ([] : expr list) (BaseT (UintT 256))
       [Return (SOME
          (Builtin (BaseT (UintT 256)) (Acc Codesize)
             [Name (BaseT AddressT) "a"]))];
     FunctionDecl External View F F "account_is_contract"
       [("a", BaseT AddressT)] ([] : expr list) (BaseT BoolT)
       [Return (SOME
          (Builtin (BaseT BoolT) (Acc IsContract)
             [Name (BaseT AddressT) "a"]))]]
End

Definition hash_builtins_program_def:
  hash_builtins_program =
    [FunctionDecl External View F F "get_block_hash"
       [("n", BaseT (UintT 256))] ([] : expr list)
       (BaseT (BytesT (Fixed 32)))
       [Return (SOME
          (Builtin (BaseT (BytesT (Fixed 32))) BlockHash
             [Name (BaseT (UintT 256)) "n"]))];
     FunctionDecl External View F F "get_blob_hash"
       [("index", BaseT (UintT 256))] ([] : expr list)
       (BaseT (BytesT (Fixed 32)))
       [Return (SOME
          (Builtin (BaseT (BytesT (Fixed 32))) BlobHash
             [Name (BaseT (UintT 256)) "index"]))]]
End

Definition ec_builtins_program_def:
  ec_builtins_program =
    [FunctionDecl External Pure F F "recover"
       [("h", BaseT (BytesT (Fixed 32)));
        ("v", BaseT (UintT 256));
        ("r", BaseT (UintT 256));
        ("s", BaseT (UintT 256))]
       ([] : expr list) (BaseT AddressT)
       [Return (SOME
          (Builtin (BaseT AddressT) ECRecover
             [Name (BaseT (BytesT (Fixed 32))) "h";
              Name (BaseT (UintT 256)) "v";
              Name (BaseT (UintT 256)) "r";
              Name (BaseT (UintT 256)) "s"]))];
     FunctionDecl External Pure F F "add_points"
       [("p", ArrayT (BaseT (UintT 256)) (Fixed 2));
        ("q", ArrayT (BaseT (UintT 256)) (Fixed 2))]
       ([] : expr list) (ArrayT (BaseT (UintT 256)) (Fixed 2))
       [Return (SOME
          (Builtin (ArrayT (BaseT (UintT 256)) (Fixed 2)) ECAdd
             [Name (ArrayT (BaseT (UintT 256)) (Fixed 2)) "p";
              Name (ArrayT (BaseT (UintT 256)) (Fixed 2)) "q"]))];
     FunctionDecl External Pure F F "multiply_point"
       [("p", ArrayT (BaseT (UintT 256)) (Fixed 2));
        ("scalar", BaseT (UintT 256))]
       ([] : expr list) (ArrayT (BaseT (UintT 256)) (Fixed 2))
       [Return (SOME
          (Builtin (ArrayT (BaseT (UintT 256)) (Fixed 2)) ECMul
             [Name (ArrayT (BaseT (UintT 256)) (Fixed 2)) "p";
              Name (BaseT (UintT 256)) "scalar"]))]]
End
