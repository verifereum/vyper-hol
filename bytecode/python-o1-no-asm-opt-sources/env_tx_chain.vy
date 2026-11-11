@external
@view
def get_gas_price() -> uint256:
    return tx.gasprice

@external
@view
def get_tx_origin() -> address:
    return tx.origin

@external
@view
def get_chain_id() -> uint256:
    return chain.id
