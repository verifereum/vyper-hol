Theory vyperStateCheckpoint
Ancestors
  vyperInterpreter vyperInterpreterCV vyperState vfmState vfmContext vfmCompute vfmTypes sptree
  jsonToVyperExpr jsonToVyperExprCV cv cv_type cv_std ASCIInumbers
Libs
  cv_transLib cv_typeLib wordsLib

(* These are the exact finite supports of the logical total maps.  Their CV
   representations already ARE sparse trees: the bridges below must remain
   proved identities, not translations of the exponential build_spt recursion.
   The account model identifies a fully empty account with absence. *)
Definition checkpoint_storage_tree_def:
  checkpoint_storage_tree (s:storage) = build_spt 0w (dimword (:256)) s
End
Definition checkpoint_accounts_tree_def:
  checkpoint_accounts_tree (a:evm_accounts) =
    build_spt empty_account_state (dimword (:160)) a
End
Definition checkpoint_transient_tree_def:
  checkpoint_transient_tree (t:transient_storage) =
    build_spt empty_storage (dimword (:160)) t
End
Definition cv_checkpoint_tree_def:
  cv_checkpoint_tree (x:cv) = x
End

val from_checkpoint_word = from_term_for ``:bytes32``;
val from_checkpoint_account = from_term_for ``:account_state``;

Theorem checkpoint_storage_tree_cv_rep[cv_rep]:
  from_sptree_sptree_spt ^from_checkpoint_word (checkpoint_storage_tree s) =
  cv_checkpoint_tree (from_storage s)
Proof
  simp[checkpoint_storage_tree_def, cv_checkpoint_tree_def, from_storage_def]
QED
Theorem checkpoint_accounts_tree_cv_rep[cv_rep]:
  from_sptree_sptree_spt ^from_checkpoint_account (checkpoint_accounts_tree a) =
  cv_checkpoint_tree (from_evm_accounts a)
Proof
  simp[checkpoint_accounts_tree_def, cv_checkpoint_tree_def, from_evm_accounts_def]
QED
Theorem checkpoint_transient_tree_cv_rep[cv_rep]:
  from_sptree_sptree_spt from_storage (checkpoint_transient_tree t) =
  cv_checkpoint_tree (from_transient_storage t)
Proof
  simp[checkpoint_transient_tree_def, cv_checkpoint_tree_def,
       from_transient_storage_def]
QED

Datatype:
  checkpoint_account = <|
    cpAddress : address;
    cpBalance : num;
    cpNonce : num;
    cpCode : byte list;
    cpStorage : (num # num) list
  |>
End
Datatype:
  state_checkpoint = <|
    cpBoundary : string;
    cpIndex : num;
    cpAccounts : checkpoint_account list;
    cpTransient : (address # num # num) list;
    cpLogs : (address # bytes32 list # byte list) list
  |>
End

Definition checkpoint_storage_def:
  checkpoint_storage s =
    MAP (λ(k,v). (k,w2n v)) (toAList (checkpoint_storage_tree s))
End
val () = cv_auto_trans checkpoint_storage_def;

Definition checkpoint_accounts_def:
  checkpoint_accounts a = MAP (λ(k,v). <|
    cpAddress := n2w k; cpBalance := v.balance; cpNonce := v.nonce;
    cpCode := v.code; cpStorage := checkpoint_storage v.storage |>)
    (toAList (checkpoint_accounts_tree a))
End
val () = cv_auto_trans checkpoint_accounts_def;

Definition checkpoint_transient_def:
  checkpoint_transient t = FLAT (MAP (λ(a,s).
    MAP (λ(k,v). (n2w a:address,k,v)) (checkpoint_storage s))
    (toAList (checkpoint_transient_tree t)))
End
val () = cv_auto_trans checkpoint_transient_def;


(* Typed cells retain the original byte/topic lists.  Rendering is confined to
   the first mismatch; successful checkpoints never format state values. *)
Datatype:
  checkpoint_field = CheckAccount | CheckBalance | CheckNonce | CheckCode
    | CheckStorage | CheckTransient | CheckLog | CheckTopics | CheckData
    | CheckDuplicate
End
Datatype:
  checkpoint_value = AbsentValue | PresentValue | NumberValue num
    | BytesValue (byte list) | TopicsValue (bytes32 list) | TextValue string
End

Definition checkpoint_field_number_def:
  checkpoint_field_number CheckAccount = 0 ∧
  checkpoint_field_number CheckBalance = 1 ∧
  checkpoint_field_number CheckNonce = 2 ∧
  checkpoint_field_number CheckCode = 3 ∧
  checkpoint_field_number CheckStorage = 4 ∧
  checkpoint_field_number CheckTransient = 5 ∧
  checkpoint_field_number CheckLog = 6 ∧
  checkpoint_field_number CheckTopics = 7 ∧
  checkpoint_field_number CheckData = 8 ∧
  checkpoint_field_number CheckDuplicate = 9
End
val () = cv_auto_trans checkpoint_field_number_def;

(* The field radix is 10 and the address radix is exactly 2^160.  NONE is
   encoded as 0, SOME n as SUC n, so no two cell keys share an index. *)
Definition checkpoint_key_def:
  checkpoint_key ((a:address),field,slot) =
    ((case slot of NONE => 0 | SOME n => SUC n) * 2 ** 160 + w2n a) * 10 +
    checkpoint_field_number field
End
val () = cv_auto_trans checkpoint_key_def;

Definition checkpoint_account_cells_def:
  checkpoint_account_cells ignored_code a =
    if a.cpBalance = 0 ∧ a.cpNonce = 0 ∧ NULL a.cpCode ∧
       EVERY (λ(k,v). v = 0) a.cpStorage then [] else
    [((a.cpAddress,CheckAccount,NONE),PresentValue);
     ((a.cpAddress,CheckBalance,NONE),NumberValue a.cpBalance);
     ((a.cpAddress,CheckNonce,NONE),NumberValue a.cpNonce)] ++
    (if MEM a.cpAddress ignored_code then []
     else [((a.cpAddress,CheckCode,NONE),BytesValue a.cpCode)]) ++
    MAP (λ(k,v). ((a.cpAddress,CheckStorage,SOME k),NumberValue v))
      (FILTER (λ(k,v). v ≠ 0) a.cpStorage)
End
val () = cv_auto_trans checkpoint_account_cells_def;

Definition checkpoint_log_cells_def:
  checkpoint_log_cells n [] = [] ∧
  checkpoint_log_cells n ((a,topics,data)::rest) =
    [(((a:address),CheckLog,SOME n),PresentValue);
     ((a,CheckTopics,SOME n),TopicsValue topics);
     ((a,CheckData,SOME n),BytesValue data)] ++
    checkpoint_log_cells (SUC n) rest
End
val () = cv_auto_trans checkpoint_log_cells_def;

Definition checkpoint_cells_def:
  checkpoint_cells ignored_code accounts transient logs =
    FLAT (MAP (checkpoint_account_cells ignored_code) accounts) ++
    MAP (λ(a,k,v). ((a,CheckTransient,SOME k),NumberValue v))
      (FILTER (λ(a,k,v). v ≠ 0) transient) ++
    checkpoint_log_cells 0 logs
End
val () = cv_auto_trans checkpoint_cells_def;

(* Sparse indexes avoid quadratic association-list lookups and duplicate
   scans.  Their keys have at most the slot width plus 165 significant bits. *)
Definition checkpoint_index_def:
  checkpoint_index [] (tree:checkpoint_value spt) = SOME tree ∧
  checkpoint_index ((key,value)::cells) tree =
    let k = checkpoint_key key in
    case lookup k tree of
    | SOME _ => NONE
    | NONE => checkpoint_index cells (insert k value tree)
End
val () = cv_auto_trans checkpoint_index_def;

Definition checkpoint_absent_value_def:
  checkpoint_absent_value ((a:address),field,(slot:num option)) =
    if field = CheckStorage ∨ field = CheckTransient
    then NumberValue 0 else AbsentValue
End
val () = cv_auto_trans checkpoint_absent_value_def;

(* The reverse pass only checks extra keys: common values were already checked
   by the forward pass, so large equal code/topic lists are compared once. *)
Definition checkpoint_first_difference_def:
  checkpoint_first_difference reversed other [] = NONE ∧
  checkpoint_first_difference reversed other ((key,value)::cells) =
    case lookup (checkpoint_key key) other of
    | SOME v =>
        if reversed ∨ value = v then
          checkpoint_first_difference reversed other cells
        else SOME (key,value,v)
    | NONE =>
        let v = checkpoint_absent_value key in
        if value = v then checkpoint_first_difference reversed other cells
        else SOME (key,if reversed then (v,value) else (value,v))
End
val checkpoint_first_difference_pre_def =
  cv_auto_trans_pre "checkpoint_first_difference_pre" checkpoint_first_difference_def;

Theorem checkpoint_first_difference_pre[cv_pre]:
  ∀reversed other cells. checkpoint_first_difference_pre reversed other cells
Proof
  ho_match_mp_tac checkpoint_first_difference_ind >> rw[] >>
  rw[Once checkpoint_first_difference_pre_def] >> fs[]
QED

Definition checkpoint_field_name_def:
  checkpoint_field_name CheckAccount = "account" ∧
  checkpoint_field_name CheckBalance = "balance" ∧
  checkpoint_field_name CheckNonce = "nonce" ∧
  checkpoint_field_name CheckCode = "code" ∧
  checkpoint_field_name CheckStorage = "storage" ∧
  checkpoint_field_name CheckTransient = "transient_storage" ∧
  checkpoint_field_name CheckLog = "log" ∧
  checkpoint_field_name CheckTopics = "log_topics" ∧
  checkpoint_field_name CheckData = "log_data" ∧
  checkpoint_field_name CheckDuplicate = "duplicate_key"
End
val () = cv_auto_trans checkpoint_field_name_def;

Definition checkpoint_value_string_def:
  checkpoint_value_string AbsentValue = "absent" ∧
  checkpoint_value_string PresentValue = "present" ∧
  checkpoint_value_string (NumberValue n) = num_to_dec_string n ∧
  checkpoint_value_string (BytesValue bs) = FLAT (MAP origin_hex_byte bs) ∧
  checkpoint_value_string (TopicsValue topics) =
    FLAT (MAP (λw. num_to_dec_string (w2n w) ++ ",") topics) ∧
  checkpoint_value_string (TextValue s) = s
End
val () = cv_auto_trans checkpoint_value_string_def;

Definition checkpoint_message_def:
  checkpoint_message cp ((addr,field,slot),expected,actual) =
    "state mismatch boundary=" ++ cp.cpBoundary ++
    " index=" ++ num_to_dec_string cp.cpIndex ++
    " address=" ++ num_to_dec_string (w2n (addr:address)) ++
    " field=" ++ checkpoint_field_name field ++ " slot=" ++
    (case slot of NONE => "none" | SOME n => num_to_dec_string n) ++
    " expected=" ++ checkpoint_value_string expected ++
    " actual=" ++ checkpoint_value_string actual
End
val () = cv_auto_trans checkpoint_message_def;

Definition compare_state_checkpoint_def:
  compare_state_checkpoint ignored_code (am:abstract_machine) cp =
    let expected = checkpoint_cells ignored_code cp.cpAccounts cp.cpTransient cp.cpLogs;
        actual = checkpoint_cells ignored_code (checkpoint_accounts am.accounts)
          (checkpoint_transient am.tStorage)
          (MAP (λe. (e.logger,e.topics,e.data)) am.logs) in
    case (checkpoint_index expected LN,checkpoint_index actual LN) of
    | (SOME expected_tree,SOME actual_tree) =>
        OPTION_MAP (checkpoint_message cp)
          (case checkpoint_first_difference F actual_tree expected of
           | SOME mismatch => SOME mismatch
           | NONE => checkpoint_first_difference T expected_tree actual)
    | _ => SOME (checkpoint_message cp
        ((0w,CheckDuplicate,NONE),TextValue "unique",TextValue "duplicate"))
End
val () = cv_auto_trans compare_state_checkpoint_def;
