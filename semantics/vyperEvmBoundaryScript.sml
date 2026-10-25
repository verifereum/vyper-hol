(*
 * Shared Verifereum boundary plumbing.
 *
 * Main definitions:
 *   make_evm_tx           — a `transaction` for one Verifereum sub-message
 *   vyper_to_tx_params    — transaction_parameters from a Vyper call_txn
 *   default_evm_gas_limit — effectively infinite gas for EVM sub-execution
 *
 * Both EVM boundaries of the Vyper semantics go through these:
 *   eval_create   (semantics/vyperCreateScript.sml)      — runs initcode
 *   eval_expr     (semantics/vyperInterpreterScript.sml) — runs callee code
 * They live here rather than in either consumer because vyperInterpreter is a
 * descendant of vyperCreate, so neither can hold the shared definition.
 *
 * TODO(semantic-limitation): the gas limit is effectively infinite; it should
 * become configurable, or be supplied by an oracle, once gas modelling for
 * Vyper-level and sub-call execution is formalized.
 *)

Theory vyperEvmBoundary
Ancestors
  arithmetic option pair rich_list words
  cv cv_std vfmState vfmContext vfmExecution[ignore_grammar] vyperContext
Libs
  cv_transLib wordsLib

(* Build the transaction for a single Verifereum sub-message.
   Fields not listed are unused placeholders in the EVM semantics.
     from:     becomes msg.sender (and the creator for CREATE/CREATE2)
     to:       becomes the address whose code runs (msgParams.callee)
     data:     becomes msg.data; creation passes []
     gasLimit: gas available for the sub-execution
     value:    becomes msg.value *)
Definition make_evm_tx_def:
  make_evm_tx caller callee value calldata gas_limit : transaction =
    <| from := caller
     ; to := SOME callee
     ; data := calldata
     ; nonce := 0
     ; value := value
     ; gasLimit := gas_limit
     ; gasPrice := 0
     ; accessList := []
     ; blobVersionedHashes := []
     ; maxFeePerBlobGas := NONE
     ; maxFeePerGas := NONE
     ; authorizationList := []
    |>
End

val () = cv_auto_trans make_evm_tx_def;

(* Build transaction_parameters from a Vyper call_txn.
   These are the transaction-level parameters that persist across calls, and
   so are shared by the creation and external-call boundaries. *)
Definition vyper_to_tx_params_def:
  vyper_to_tx_params (txn: call_txn) : transaction_parameters =
    <| origin := txn.origin
     ; gasPrice := txn.gas_price
     ; baseFeePerGas := txn.base_fee
     ; baseFeePerBlobGas := txn.blob_base_fee
     ; blockNumber := txn.block_number
     ; blockTimeStamp := txn.time_stamp
     ; blockCoinBase := txn.coinbase
     ; blockGasLimit := txn.gas_limit
     ; prevRandao := n2w txn.prev_randao
     ; prevHashes := txn.block_hashes
     ; blobHashes := txn.blob_hashes
     ; chainId := txn.chain_id
     ; authRefund := 0
    |>
End

val () = cv_auto_trans vyper_to_tx_params_def;

(* Effectively infinite gas for EVM sub-execution. *)
Definition default_evm_gas_limit_def:
  default_evm_gas_limit : num = 2 ** 64
End

val () = cv_auto_trans default_evm_gas_limit_def;