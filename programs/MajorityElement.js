environment({
  current: array([int32], 1),
  count: array([int32], 1),
  scratchpad: array([int8], 1024),
  member: array([int256], 200)
})

procedure('main', { what: int32, absolute: address }, () => {
  // extract number from calldata
  store("member", 0, [2])
  set(
    'what',
    (coerceInt32(retrieve(0)) << coerceInt32(24)) +
      (coerceInt32(retrieve(1)) << coerceInt32(16)) +
      (coerceInt32(retrieve(2)) << coerceInt32(8)) +
      coerceInt32(retrieve(3))
  )

  if (retrieve("count", 0)[0] == coerceInt32(0)) {
    store("current", 0, [get("what")])
  }

  if (get("what") == retrieve("current", 0)[0]) {
    store("count", 0, [retrieve("count", 0)[0] + coerceInt32(1)])
  } else {
    store("count", 0, [retrieve("count", 0)[0] - coerceInt32(1)])
  }

  store(0, retrieve("count", 0)[0] >> coerceInt32(24))
  store(1, retrieve("count", 0)[0] >> coerceInt32(16) & coerceInt32(255))
  store(2, retrieve("count", 0)[0] >> coerceInt32(8) & coerceInt32(255))
  store(3, retrieve("count", 0)[0] & coerceInt32(255))

  donate(get("absolute"), coerceInt256(2000))
  invoke(get("absolute"), coerceInt256(2000), "scratchpad", coerceInt64(1024))
  invoke(getSender(), getMoney(), "scratchpad", coerceInt64(1024))
  invoke(address(
    coerceInt8(0),
    coerceInt8(0),
    coerceInt8(0),
    coerceInt8(0),
    coerceInt8(0),
    coerceInt8(0),
    coerceInt8(0),
    coerceInt8(0),
    coerceInt8(0),
    coerceInt8(0),
    coerceInt8(0),
    coerceInt8(0),
    coerceInt8(0),
    coerceInt8(0),
    coerceInt8(0),
    coerceInt8(0),
    coerceInt8(0),
    coerceInt8(0),
    coerceInt8(0),
    coerceInt8(0)
  ), getMoney(), "scratchpad", coerceInt64(1024))
})
