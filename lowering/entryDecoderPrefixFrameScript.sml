(* Resource transport along operational prefixes. These rules leave semantic
   step preservation explicit: allocation-map inclusion is not history. *)
Theory entryDecoderPrefixFrame
Ancestors
  abiEncoderObserver allocaHistory exprLoweringProps abiDecoderFrame

Theorem decoder_local_prefix_invariant:
  !ctx fn cut s t. local_prefix ctx fn cut s t ==>
  !P. P s /\
    (!a b. abi_observer_step ctx fn cut a b /\ P a ==> P b) ==> P t
Proof
  Induct_on `local_prefix` >> metis_tac[]
QED

Theorem decoder_local_prefix_region_invariant:
  local_prefix ctx fn cut s t /\ region s /\ P s /\
  (!a b. abi_observer_step ctx fn cut a b /\ region a ==> region b) /\
  (!a b. abi_observer_step ctx fn cut a b /\ region a /\ P a ==> P b) ==>
  region t /\ P t
Proof
  strip_tac >> drule decoder_local_prefix_invariant >>
  disch_then (qspec_then `\u. region u /\ P u` mp_tac) >>
  simp[] >> metis_tac[]
QED

(* History is cursor-sensitive. Its step obligation includes alloca_inv;
   room and source-frame predicates must be established at every reached node.
   The generic frame parameter can include source locals, immutables, etc. *)
Theorem decoder_local_prefix_resources:
  local_prefix ctx fn cut s t /\ region s /\
  alloca_inv s /\ alloca_history fn s /\
  alloca_room ctx fn s /\ fmp_room ctx fn s /\ frame s /\
  (!a b. abi_observer_step ctx fn cut a b /\ region a ==> region b) /\
  (!a b. abi_observer_step ctx fn cut a b /\ region a /\ alloca_inv a ==>
    alloca_inv b) /\
  (!a b. abi_observer_step ctx fn cut a b /\ region a /\ alloca_inv a /\
    alloca_history fn a ==> alloca_history fn b) /\
  (!a b. abi_observer_step ctx fn cut a b /\ region a /\ alloca_inv a /\
    alloca_room ctx fn a ==> alloca_room ctx fn b) /\
  (!a b. abi_observer_step ctx fn cut a b /\ region a /\ alloca_inv a /\
    fmp_room ctx fn a ==> fmp_room ctx fn b) /\
  (!a b. abi_observer_step ctx fn cut a b /\ region a /\ frame a ==> frame b) ==>
  region t /\ alloca_inv t /\ alloca_history fn t /\
  alloca_room ctx fn t /\ fmp_room ctx fn t /\ frame t
Proof
  strip_tac >> drule decoder_local_prefix_invariant >>
  disch_then (qspec_then `\u. region u /\ alloca_inv u /\ alloca_history fn u /\
    alloca_room ctx fn u /\ fmp_room ctx fn u /\ frame u` mp_tac) >>
  simp[] >> metis_tac[]
QED
