---- MODULE AbstractMempoolSpecFiniteApalache ----

EXTENDS Apalache

CONSTANT 
  \* @type: Set(PAYLOAD);
  MCPayload

VARIABLE
  \* @type: Set(PAYLOAD);
  MCmempool 



INSTANCE AbstractMempoolSpecFinite WITH
  Payload <- MCPayload,
  mempool <- MCmempool

ConstInit == MCPayload = {"1_OF_PAYLOAD","2_OF_PAYLOAD","3_OF_PAYLOAD","4_OF_PAYLOAD"}


====
