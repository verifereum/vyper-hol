@external
@view
def get_timestamp() -> uint256:
    return block.timestamp

@external
@view
def get_block_number() -> uint256:
    return block.number

@external
@view
def get_blob_base_fee() -> uint256:
    return block.blobbasefee

@external
@view
def get_previous_hash() -> bytes32:
    return block.prevhash

@external
@view
def get_coinbase() -> address:
    return block.coinbase

@external
@view
def get_gas_limit() -> uint256:
    return block.gaslimit

@external
@view
def get_base_fee() -> uint256:
    return block.basefee

@external
@view
def get_difficulty() -> uint256:
    return block.difficulty
