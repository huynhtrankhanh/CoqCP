environment({
  dp: array([int64], 1000000),
  message: array([int32], 1),
  n: array([int64], 1),
})

procedure('get weight', { index: int64 }, () => {
  store('message', 0, [
    coerceInt32(retrieve(4 * get('index'))) * coerceInt32(1 << 24) +
      coerceInt32(retrieve(4 * get('index') + 1)) * coerceInt32(1 << 16) +
      coerceInt32(retrieve(4 * get('index') + 2)) * coerceInt32(1 << 8) +
      coerceInt32(retrieve(4 * get('index') + 3)),
  ])
})

procedure('get value', { index: int64 }, () => {
  store('message', 0, [
    coerceInt32(retrieve(4 * retrieve('n', 0)[0] + 4 * get('index'))) *
      coerceInt32(1 << 24) +
      coerceInt32(retrieve(4 * retrieve('n', 0)[0] + 4 * get('index') + 1)) *
        coerceInt32(1 << 16) +
      coerceInt32(retrieve(4 * retrieve('n', 0)[0] + 4 * get('index') + 2)) *
        coerceInt32(1 << 8) +
      coerceInt32(retrieve(4 * retrieve('n', 0)[0] + 4 * get('index') + 3)),
  ])
})

procedure('store result', { x: int64 }, () => {
  store(0, coerceInt8(get('x') >> 56))
  store(1, coerceInt8((get('x') >> 48) & 255))
  store(2, coerceInt8((get('x') >> 40) & 255))
  store(3, coerceInt8((get('x') >> 32) & 255))
  store(4, coerceInt8((get('x') >> 24) & 255))
  store(5, coerceInt8((get('x') >> 16) & 255))
  store(6, coerceInt8((get('x') >> 8) & 255))
  store(7, coerceInt8(get('x') & 255))
})

procedure('get limit', {}, () => {
  store('message', 0, [
    coerceInt32(retrieve(8 * retrieve('n', 0)[0])) * coerceInt32(1 << 24)
    + coerceInt32(retrieve(8 * retrieve('n', 0)[0])) * coerceInt32(1 << 16)
    + coerceInt32(retrieve(8 * retrieve('n', 0)[0])) * coerceInt32(1 << 8)
    + coerceInt32(retrieve(8 * retrieve('n', 0)[0]))
  ])
})

procedure('main', { }, () => {
  store('n', 0, [divide(communicationSize() - 4, 8)])
  
})
